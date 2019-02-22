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
    let uu____68694 =
      let uu____68695 = FStar_Tactics_Types.goal_env g  in
      let uu____68696 = FStar_Tactics_Types.goal_type g  in
      bnorm uu____68695 uu____68696  in
    FStar_Tactics_Types.goal_with_type g uu____68694
  
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
      let uu____68810 = FStar_Options.tactics_failhard ()  in
      if uu____68810
      then run t p
      else
        (try (fun uu___640_68820  -> match () with | () -> run t p) ()
         with
         | FStar_Errors.Err (uu____68829,msg) ->
             FStar_Tactics_Result.Failed
               ((FStar_Tactics_Types.TacticFailure msg), p)
         | FStar_Errors.Error (uu____68833,msg,uu____68835) ->
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
           let uu____68915 = run t1 p  in
           match uu____68915 with
           | FStar_Tactics_Result.Success (a,q) ->
               let uu____68922 = t2 a  in run uu____68922 q
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
    let uu____68945 =
      FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head  in
    match uu____68945 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (check_goal_solved :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun goal  -> get_uvar_solved goal.FStar_Tactics_Types.goal_ctx_uvar 
let (goal_to_string_verbose : FStar_Tactics_Types.goal -> Prims.string) =
  fun g  ->
    let uu____68967 =
      FStar_Syntax_Print.ctx_uvar_to_string
        g.FStar_Tactics_Types.goal_ctx_uvar
       in
    let uu____68969 =
      let uu____68971 = check_goal_solved g  in
      match uu____68971 with
      | FStar_Pervasives_Native.None  -> ""
      | FStar_Pervasives_Native.Some t ->
          let uu____68977 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "\tGOAL ALREADY SOLVED!: %s" uu____68977
       in
    FStar_Util.format2 "%s%s\n" uu____68967 uu____68969
  
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
            let uu____69024 = FStar_Options.print_implicits ()  in
            if uu____69024
            then
              let uu____69028 = FStar_Tactics_Types.goal_env g  in
              let uu____69029 = FStar_Tactics_Types.goal_witness g  in
              tts uu____69028 uu____69029
            else
              (let uu____69032 =
                 get_uvar_solved g.FStar_Tactics_Types.goal_ctx_uvar  in
               match uu____69032 with
               | FStar_Pervasives_Native.None  -> "_"
               | FStar_Pervasives_Native.Some t ->
                   let uu____69038 = FStar_Tactics_Types.goal_env g  in
                   let uu____69039 = FStar_Tactics_Types.goal_witness g  in
                   tts uu____69038 uu____69039)
             in
          let num =
            match maybe_num with
            | FStar_Pervasives_Native.None  -> ""
            | FStar_Pervasives_Native.Some (i,n1) ->
                let uu____69062 = FStar_Util.string_of_int i  in
                let uu____69064 = FStar_Util.string_of_int n1  in
                FStar_Util.format2 " %s/%s" uu____69062 uu____69064
             in
          let maybe_label =
            match g.FStar_Tactics_Types.label with
            | "" -> ""
            | l -> Prims.op_Hat " (" (Prims.op_Hat l ")")  in
          let actual_goal =
            if ps.FStar_Tactics_Types.tac_verb_dbg
            then goal_to_string_verbose g
            else
              (let uu____69082 =
                 FStar_Syntax_Print.binders_to_string ", "
                   (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
                  in
               let uu____69085 =
                 let uu____69087 = FStar_Tactics_Types.goal_env g  in
                 tts uu____69087
                   (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                  in
               FStar_Util.format3 "%s |- %s : %s\n" uu____69082 w uu____69085)
             in
          FStar_Util.format4 "%s%s%s:\n%s\n" kind num maybe_label actual_goal
  
let (tacprint : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      let uu____69114 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____69114
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____69139 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____69139
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____69171 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____69171
  
let (comp_to_typ : FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____69181) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____69191) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (get_phi :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun g  ->
    let uu____69211 =
      let uu____69212 = FStar_Tactics_Types.goal_env g  in
      let uu____69213 = FStar_Tactics_Types.goal_type g  in
      FStar_TypeChecker_Normalize.unfold_whnf uu____69212 uu____69213  in
    FStar_Syntax_Util.un_squash uu____69211
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  -> let uu____69222 = get_phi g  in FStar_Option.isSome uu____69222 
let (print : Prims.string -> unit tac) = fun msg  -> tacprint msg; ret () 
let (debugging : unit -> Prims.bool tac) =
  fun uu____69246  ->
    bind get
      (fun ps  ->
         let uu____69254 =
           FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
             (FStar_Options.Other "Tac")
            in
         ret uu____69254)
  
let (ps_to_string :
  (Prims.string * FStar_Tactics_Types.proofstate) -> Prims.string) =
  fun uu____69269  ->
    match uu____69269 with
    | (msg,ps) ->
        let p_imp imp =
          FStar_Syntax_Print.uvar_to_string
            (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
           in
        let n_active = FStar_List.length ps.FStar_Tactics_Types.goals  in
        let n_smt = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
        let n1 = n_active + n_smt  in
        let uu____69301 =
          let uu____69305 =
            let uu____69309 =
              let uu____69311 =
                FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
              FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____69311
                msg
               in
            let uu____69314 =
              let uu____69318 =
                if
                  ps.FStar_Tactics_Types.entry_range <>
                    FStar_Range.dummyRange
                then
                  let uu____69322 =
                    FStar_Range.string_of_def_range
                      ps.FStar_Tactics_Types.entry_range
                     in
                  FStar_Util.format1 "Location: %s\n" uu____69322
                else ""  in
              let uu____69328 =
                let uu____69332 =
                  let uu____69334 =
                    FStar_TypeChecker_Env.debug
                      ps.FStar_Tactics_Types.main_context
                      (FStar_Options.Other "Imp")
                     in
                  if uu____69334
                  then
                    let uu____69339 =
                      FStar_Common.string_of_list p_imp
                        ps.FStar_Tactics_Types.all_implicits
                       in
                    FStar_Util.format1 "Imps: %s\n" uu____69339
                  else ""  in
                [uu____69332]  in
              uu____69318 :: uu____69328  in
            uu____69309 :: uu____69314  in
          let uu____69349 =
            let uu____69353 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "Goal"
                       (FStar_Pervasives_Native.Some
                          (((Prims.parse_int "1") + i), n1)) ps g)
                ps.FStar_Tactics_Types.goals
               in
            let uu____69373 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "SMT Goal"
                       (FStar_Pervasives_Native.Some
                          ((((Prims.parse_int "1") + n_active) + i), n1)) ps
                       g) ps.FStar_Tactics_Types.smt_goals
               in
            FStar_List.append uu____69353 uu____69373  in
          FStar_List.append uu____69305 uu____69349  in
        FStar_String.concat "" uu____69301
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      let uu____69407 =
        let uu____69408 = FStar_Tactics_Types.goal_env g  in
        FStar_TypeChecker_Env.all_binders uu____69408  in
      let uu____69409 =
        let uu____69414 =
          let uu____69415 = FStar_Tactics_Types.goal_env g  in
          FStar_TypeChecker_Env.dsenv uu____69415  in
        FStar_Syntax_Print.binders_to_json uu____69414  in
      FStar_All.pipe_right uu____69407 uu____69409  in
    let uu____69416 =
      let uu____69424 =
        let uu____69432 =
          let uu____69438 =
            let uu____69439 =
              let uu____69447 =
                let uu____69453 =
                  let uu____69454 =
                    let uu____69456 = FStar_Tactics_Types.goal_env g  in
                    let uu____69457 = FStar_Tactics_Types.goal_witness g  in
                    tts uu____69456 uu____69457  in
                  FStar_Util.JsonStr uu____69454  in
                ("witness", uu____69453)  in
              let uu____69460 =
                let uu____69468 =
                  let uu____69474 =
                    let uu____69475 =
                      let uu____69477 = FStar_Tactics_Types.goal_env g  in
                      let uu____69478 = FStar_Tactics_Types.goal_type g  in
                      tts uu____69477 uu____69478  in
                    FStar_Util.JsonStr uu____69475  in
                  ("type", uu____69474)  in
                [uu____69468;
                ("label", (FStar_Util.JsonStr (g.FStar_Tactics_Types.label)))]
                 in
              uu____69447 :: uu____69460  in
            FStar_Util.JsonAssoc uu____69439  in
          ("goal", uu____69438)  in
        [uu____69432]  in
      ("hyps", g_binders) :: uu____69424  in
    FStar_Util.JsonAssoc uu____69416
  
let (ps_to_json :
  (Prims.string * FStar_Tactics_Types.proofstate) -> FStar_Util.json) =
  fun uu____69532  ->
    match uu____69532 with
    | (msg,ps) ->
        let uu____69542 =
          let uu____69550 =
            let uu____69558 =
              let uu____69566 =
                let uu____69574 =
                  let uu____69580 =
                    let uu____69581 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____69581  in
                  ("goals", uu____69580)  in
                let uu____69586 =
                  let uu____69594 =
                    let uu____69600 =
                      let uu____69601 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____69601  in
                    ("smt-goals", uu____69600)  in
                  [uu____69594]  in
                uu____69574 :: uu____69586  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____69566
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____69558  in
          let uu____69635 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____69651 =
                let uu____69657 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____69657)  in
              [uu____69651]
            else []  in
          FStar_List.append uu____69550 uu____69635  in
        FStar_Util.JsonAssoc uu____69542
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____69697  ->
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
         (let uu____69728 = FStar_Tactics_Types.subst_proof_state subst1 ps
             in
          dump_proofstate uu____69728 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let traise : 'a . Prims.exn -> 'a tac =
  fun e  -> mk_tac (fun ps  -> FStar_Tactics_Result.Failed (e, ps)) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____69801 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____69801
          then dump_proofstate ps (Prims.op_Hat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed
           ((FStar_Tactics_Types.TacticFailure msg), ps))
  
let fail1 : 'Auu____69815 . Prims.string -> Prims.string -> 'Auu____69815 tac
  =
  fun msg  ->
    fun x  -> let uu____69832 = FStar_Util.format1 msg x  in fail uu____69832
  
let fail2 :
  'Auu____69843 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____69843 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        let uu____69867 = FStar_Util.format2 msg x y  in fail uu____69867
  
let fail3 :
  'Auu____69880 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____69880 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____69911 = FStar_Util.format3 msg x y z  in fail uu____69911
  
let fail4 :
  'Auu____69926 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____69926 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____69964 = FStar_Util.format4 msg x y z w  in
            fail uu____69964
  
let catch : 'a . 'a tac -> (Prims.exn,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____69999 = run t ps  in
         match uu____69999 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___802_70023 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___802_70023.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___802_70023.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___802_70023.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___802_70023.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___802_70023.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___802_70023.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___802_70023.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___802_70023.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___802_70023.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___802_70023.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___802_70023.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (uu___802_70023.FStar_Tactics_Types.local_state)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let recover : 'a . 'a tac -> (Prims.exn,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let uu____70062 = run t ps  in
         match uu____70062 with
         | FStar_Tactics_Result.Success (a,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inr a), q)
         | FStar_Tactics_Result.Failed (m,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inl m), q))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____70110 = catch t  in
    bind uu____70110
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____70137 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try
           (fun uu___828_70169  ->
              match () with
              | () -> let uu____70174 = trytac t  in run uu____70174 ps) ()
         with
         | FStar_Errors.Err (uu____70190,msg) ->
             (log ps
                (fun uu____70196  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____70202,msg,uu____70204) ->
             (log ps
                (fun uu____70209  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____70246 = run t ps  in
           match uu____70246 with
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
  fun p  -> mk_tac (fun uu____70270  -> FStar_Tactics_Result.Success ((), p)) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___863_70285 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___863_70285.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___863_70285.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___863_70285.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___863_70285.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___863_70285.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___863_70285.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___863_70285.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___863_70285.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___863_70285.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___863_70285.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___863_70285.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___863_70285.FStar_Tactics_Types.local_state)
            }))
  
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____70309 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____70309
         then
           let uu____70313 = FStar_Syntax_Print.term_to_string t1  in
           let uu____70315 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____70313
             uu____70315
         else ());
        (try
           (fun uu___871_70326  ->
              match () with
              | () ->
                  let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
                  ((let uu____70334 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____70334
                    then
                      let uu____70338 =
                        FStar_Common.string_of_option
                          (FStar_TypeChecker_Rel.guard_to_string env) res
                         in
                      let uu____70340 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____70342 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.print3
                        "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____70338
                        uu____70340 uu____70342
                    else ());
                   (match res with
                    | FStar_Pervasives_Native.None  -> ret false
                    | FStar_Pervasives_Native.Some g ->
                        let uu____70353 =
                          add_implicits g.FStar_TypeChecker_Env.implicits  in
                        bind uu____70353 (fun uu____70358  -> ret true)))) ()
         with
         | FStar_Errors.Err (uu____70368,msg) ->
             mlog
               (fun uu____70374  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____70377  -> ret false)
         | FStar_Errors.Error (uu____70380,msg,r) ->
             mlog
               (fun uu____70388  ->
                  let uu____70389 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____70389) (fun uu____70393  -> ret false))
  
let (compress_implicits : unit tac) =
  bind get
    (fun ps  ->
       let imps = ps.FStar_Tactics_Types.all_implicits  in
       let g =
         let uu___897_70407 = FStar_TypeChecker_Env.trivial_guard  in
         {
           FStar_TypeChecker_Env.guard_f =
             (uu___897_70407.FStar_TypeChecker_Env.guard_f);
           FStar_TypeChecker_Env.deferred =
             (uu___897_70407.FStar_TypeChecker_Env.deferred);
           FStar_TypeChecker_Env.univ_ineqs =
             (uu___897_70407.FStar_TypeChecker_Env.univ_ineqs);
           FStar_TypeChecker_Env.implicits = imps
         }  in
       let g1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g
          in
       let ps' =
         let uu___901_70410 = ps  in
         {
           FStar_Tactics_Types.main_context =
             (uu___901_70410.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___901_70410.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (g1.FStar_TypeChecker_Env.implicits);
           FStar_Tactics_Types.goals =
             (uu___901_70410.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___901_70410.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___901_70410.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___901_70410.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___901_70410.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___901_70410.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___901_70410.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___901_70410.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___901_70410.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___901_70410.FStar_Tactics_Types.local_state)
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
          (fun uu____70437  ->
             (let uu____70439 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____70439
              then
                (FStar_Options.push ();
                 (let uu____70444 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____70448 = __do_unify env t1 t2  in
              bind uu____70448
                (fun r  ->
                   (let uu____70459 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____70459 then FStar_Options.pop () else ());
                   ret r)))
  
let (remove_solved_goals : unit tac) =
  bind get
    (fun ps  ->
       let ps' =
         let uu___916_70473 = ps  in
         let uu____70474 =
           FStar_List.filter
             (fun g  ->
                let uu____70480 = check_goal_solved g  in
                FStar_Option.isNone uu____70480) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___916_70473.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___916_70473.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___916_70473.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____70474;
           FStar_Tactics_Types.smt_goals =
             (uu___916_70473.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___916_70473.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___916_70473.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___916_70473.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___916_70473.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___916_70473.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___916_70473.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___916_70473.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___916_70473.FStar_Tactics_Types.local_state)
         }  in
       set ps')
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____70498 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____70498 with
      | FStar_Pervasives_Native.Some uu____70503 ->
          let uu____70504 =
            let uu____70506 = goal_to_string_verbose goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____70506  in
          fail uu____70504
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____70527 = FStar_Tactics_Types.goal_env goal  in
      let uu____70528 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____70527 solution uu____70528
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____70535 =
         let uu___929_70536 = p  in
         let uu____70537 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___929_70536.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___929_70536.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___929_70536.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____70537;
           FStar_Tactics_Types.smt_goals =
             (uu___929_70536.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___929_70536.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___929_70536.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___929_70536.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___929_70536.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___929_70536.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___929_70536.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___929_70536.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___929_70536.FStar_Tactics_Types.local_state)
         }  in
       set uu____70535)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      mlog
        (fun uu____70559  ->
           let uu____70560 =
             let uu____70562 = FStar_Tactics_Types.goal_witness goal  in
             FStar_Syntax_Print.term_to_string uu____70562  in
           let uu____70563 = FStar_Syntax_Print.term_to_string solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____70560 uu____70563)
        (fun uu____70568  ->
           let uu____70569 = trysolve goal solution  in
           bind uu____70569
             (fun b  ->
                if b
                then bind __dismiss (fun uu____70581  -> remove_solved_goals)
                else
                  (let uu____70584 =
                     let uu____70586 =
                       let uu____70588 = FStar_Tactics_Types.goal_env goal
                          in
                       tts uu____70588 solution  in
                     let uu____70589 =
                       let uu____70591 = FStar_Tactics_Types.goal_env goal
                          in
                       let uu____70592 =
                         FStar_Tactics_Types.goal_witness goal  in
                       tts uu____70591 uu____70592  in
                     let uu____70593 =
                       let uu____70595 = FStar_Tactics_Types.goal_env goal
                          in
                       let uu____70596 = FStar_Tactics_Types.goal_type goal
                          in
                       tts uu____70595 uu____70596  in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____70586 uu____70589 uu____70593
                      in
                   fail uu____70584)))
  
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____70613 = set_solution goal solution  in
      bind uu____70613
        (fun uu____70617  ->
           bind __dismiss (fun uu____70619  -> remove_solved_goals))
  
let (set_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___945_70638 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___945_70638.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___945_70638.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___945_70638.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals = gs;
              FStar_Tactics_Types.smt_goals =
                (uu___945_70638.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___945_70638.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___945_70638.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___945_70638.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___945_70638.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___945_70638.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___945_70638.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___945_70638.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___945_70638.FStar_Tactics_Types.local_state)
            }))
  
let (set_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___949_70657 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___949_70657.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___949_70657.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___949_70657.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___949_70657.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals = gs;
              FStar_Tactics_Types.depth =
                (uu___949_70657.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___949_70657.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___949_70657.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___949_70657.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___949_70657.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___949_70657.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___949_70657.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___949_70657.FStar_Tactics_Types.local_state)
            }))
  
let (dismiss_all : unit tac) = set_goals [] 
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____70684 = FStar_Options.defensive ()  in
    if uu____70684
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____70694 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____70694)
         in
      let b2 =
        b1 &&
          (let uu____70698 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____70698)
         in
      let rec aux b3 e =
        let uu____70713 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____70713 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____70733 =
        (let uu____70737 = aux b2 env  in Prims.op_Negation uu____70737) &&
          (let uu____70740 = FStar_ST.op_Bang nwarn  in
           uu____70740 < (Prims.parse_int "5"))
         in
      (if uu____70733
       then
         ((let uu____70766 =
             let uu____70767 = FStar_Tactics_Types.goal_type g  in
             uu____70767.FStar_Syntax_Syntax.pos  in
           let uu____70770 =
             let uu____70776 =
               let uu____70778 = goal_to_string_verbose g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____70778
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____70776)  in
           FStar_Errors.log_issue uu____70766 uu____70770);
          (let uu____70782 =
             let uu____70784 = FStar_ST.op_Bang nwarn  in
             uu____70784 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____70782))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___971_70853 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___971_70853.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___971_70853.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___971_70853.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___971_70853.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___971_70853.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___971_70853.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___971_70853.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___971_70853.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___971_70853.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___971_70853.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___971_70853.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___971_70853.FStar_Tactics_Types.local_state)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___976_70874 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___976_70874.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___976_70874.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___976_70874.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___976_70874.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___976_70874.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___976_70874.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___976_70874.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___976_70874.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___976_70874.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___976_70874.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___976_70874.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___976_70874.FStar_Tactics_Types.local_state)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___981_70895 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___981_70895.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___981_70895.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___981_70895.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___981_70895.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___981_70895.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___981_70895.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___981_70895.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___981_70895.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___981_70895.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___981_70895.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___981_70895.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___981_70895.FStar_Tactics_Types.local_state)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___986_70916 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___986_70916.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___986_70916.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___986_70916.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___986_70916.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___986_70916.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___986_70916.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___986_70916.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___986_70916.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___986_70916.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___986_70916.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___986_70916.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___986_70916.FStar_Tactics_Types.local_state)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____70928  -> add_goals [g]) 
let (new_uvar :
  Prims.string ->
    env ->
      FStar_Reflection_Data.typ ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar) tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____70959 =
          FStar_TypeChecker_Env.new_implicit_var_aux reason
            typ.FStar_Syntax_Syntax.pos env typ
            FStar_Syntax_Syntax.Allow_untyped FStar_Pervasives_Native.None
           in
        match uu____70959 with
        | (u,ctx_uvar,g_u) ->
            let uu____70997 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____70997
              (fun uu____71006  ->
                 let uu____71007 =
                   let uu____71012 =
                     let uu____71013 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____71013  in
                   (u, uu____71012)  in
                 ret uu____71007)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____71034 = FStar_Syntax_Util.un_squash t1  in
    match uu____71034 with
    | FStar_Pervasives_Native.Some t' ->
        let t'1 = FStar_Syntax_Util.unascribe t'  in
        let uu____71046 =
          let uu____71047 = FStar_Syntax_Subst.compress t'1  in
          uu____71047.FStar_Syntax_Syntax.n  in
        (match uu____71046 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____71052 -> false)
    | uu____71054 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____71067 = FStar_Syntax_Util.un_squash t  in
    match uu____71067 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____71078 =
          let uu____71079 = FStar_Syntax_Subst.compress t'  in
          uu____71079.FStar_Syntax_Syntax.n  in
        (match uu____71078 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____71084 -> false)
    | uu____71086 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____71099  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____71111 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____71111 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____71118 = goal_to_string_verbose hd1  in
                    let uu____71120 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____71118 uu____71120);
                   ret hd1)))
  
let (tadmit_t : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____71133 =
      bind get
        (fun ps  ->
           let uu____71139 = cur_goal ()  in
           bind uu____71139
             (fun g  ->
                (let uu____71146 =
                   let uu____71147 = FStar_Tactics_Types.goal_type g  in
                   uu____71147.FStar_Syntax_Syntax.pos  in
                 let uu____71150 =
                   let uu____71156 =
                     let uu____71158 =
                       goal_to_string "" FStar_Pervasives_Native.None ps g
                        in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____71158
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____71156)  in
                 FStar_Errors.log_issue uu____71146 uu____71150);
                solve' g t))
       in
    FStar_All.pipe_left (wrap_err "tadmit_t") uu____71133
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____71181  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___1031_71192 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___1031_71192.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___1031_71192.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___1031_71192.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___1031_71192.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___1031_71192.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___1031_71192.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___1031_71192.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___1031_71192.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___1031_71192.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___1031_71192.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___1031_71192.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (uu___1031_71192.FStar_Tactics_Types.local_state)
           }  in
         let uu____71194 = set ps1  in
         bind uu____71194
           (fun uu____71199  ->
              let uu____71200 = FStar_BigInt.of_int_fs n1  in ret uu____71200))
  
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
              let uu____71238 = env.FStar_TypeChecker_Env.universe_of env phi
                 in
              FStar_Syntax_Util.mk_squash uu____71238 phi  in
            let uu____71239 = new_uvar reason env typ  in
            bind uu____71239
              (fun uu____71254  ->
                 match uu____71254 with
                 | (uu____71261,ctx_uvar) ->
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
             (fun uu____71308  ->
                let uu____71309 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____71309)
             (fun uu____71314  ->
                let e1 =
                  let uu___1049_71316 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1049_71316.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1049_71316.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1049_71316.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1049_71316.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1049_71316.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1049_71316.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1049_71316.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1049_71316.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1049_71316.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1049_71316.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1049_71316.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1049_71316.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1049_71316.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1049_71316.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1049_71316.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1049_71316.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1049_71316.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1049_71316.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1049_71316.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1049_71316.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1049_71316.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1049_71316.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1049_71316.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1049_71316.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1049_71316.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1049_71316.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1049_71316.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1049_71316.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1049_71316.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1049_71316.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1049_71316.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1049_71316.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1049_71316.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1049_71316.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1049_71316.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1049_71316.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1049_71316.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1049_71316.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1049_71316.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1049_71316.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1049_71316.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1049_71316.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___1053_71328  ->
                     match () with
                     | () ->
                         let uu____71337 =
                           FStar_TypeChecker_TcTerm.type_of_tot_term e1 t  in
                         ret uu____71337) ()
                with
                | FStar_Errors.Err (uu____71364,msg) ->
                    let uu____71368 = tts e1 t  in
                    let uu____71370 =
                      let uu____71372 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____71372
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____71368 uu____71370 msg
                | FStar_Errors.Error (uu____71382,msg,uu____71384) ->
                    let uu____71387 = tts e1 t  in
                    let uu____71389 =
                      let uu____71391 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____71391
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____71387 uu____71389 msg))
  
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
             (fun uu____71444  ->
                let uu____71445 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc_ghost(%s)\n" uu____71445)
             (fun uu____71450  ->
                let e1 =
                  let uu___1070_71452 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1070_71452.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1070_71452.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1070_71452.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1070_71452.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1070_71452.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1070_71452.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1070_71452.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1070_71452.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1070_71452.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1070_71452.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1070_71452.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1070_71452.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1070_71452.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1070_71452.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1070_71452.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1070_71452.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1070_71452.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1070_71452.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1070_71452.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1070_71452.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1070_71452.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1070_71452.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1070_71452.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1070_71452.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1070_71452.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1070_71452.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1070_71452.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1070_71452.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1070_71452.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1070_71452.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1070_71452.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1070_71452.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1070_71452.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1070_71452.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1070_71452.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1070_71452.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1070_71452.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1070_71452.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1070_71452.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1070_71452.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1070_71452.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1070_71452.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___1074_71467  ->
                     match () with
                     | () ->
                         let uu____71476 =
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e1 t
                            in
                         (match uu____71476 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____71514,msg) ->
                    let uu____71518 = tts e1 t  in
                    let uu____71520 =
                      let uu____71522 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____71522
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____71518 uu____71520 msg
                | FStar_Errors.Error (uu____71532,msg,uu____71534) ->
                    let uu____71537 = tts e1 t  in
                    let uu____71539 =
                      let uu____71541 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____71541
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____71537 uu____71539 msg))
  
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
             (fun uu____71594  ->
                let uu____71595 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____71595)
             (fun uu____71601  ->
                let e1 =
                  let uu___1095_71603 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1095_71603.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1095_71603.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1095_71603.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1095_71603.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1095_71603.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1095_71603.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1095_71603.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1095_71603.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1095_71603.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1095_71603.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1095_71603.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1095_71603.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1095_71603.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1095_71603.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1095_71603.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1095_71603.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1095_71603.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1095_71603.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1095_71603.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1095_71603.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1095_71603.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1095_71603.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1095_71603.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1095_71603.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1095_71603.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1095_71603.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1095_71603.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1095_71603.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1095_71603.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1095_71603.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1095_71603.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1095_71603.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1095_71603.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1095_71603.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1095_71603.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1095_71603.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1095_71603.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1095_71603.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1095_71603.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1095_71603.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1095_71603.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1095_71603.FStar_TypeChecker_Env.nbe)
                  }  in
                let e2 =
                  let uu___1098_71606 = e1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1098_71606.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1098_71606.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1098_71606.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1098_71606.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1098_71606.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1098_71606.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1098_71606.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1098_71606.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1098_71606.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1098_71606.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1098_71606.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1098_71606.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1098_71606.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1098_71606.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1098_71606.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1098_71606.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1098_71606.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1098_71606.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1098_71606.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1098_71606.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1098_71606.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1098_71606.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1098_71606.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1098_71606.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___1098_71606.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1098_71606.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1098_71606.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1098_71606.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1098_71606.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1098_71606.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1098_71606.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1098_71606.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1098_71606.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1098_71606.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1098_71606.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1098_71606.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1098_71606.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1098_71606.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1098_71606.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1098_71606.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1098_71606.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1098_71606.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___1102_71621  ->
                     match () with
                     | () ->
                         let uu____71630 =
                           FStar_TypeChecker_TcTerm.tc_term e2 t  in
                         (match uu____71630 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____71668,msg) ->
                    let uu____71672 = tts e2 t  in
                    let uu____71674 =
                      let uu____71676 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____71676
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____71672 uu____71674 msg
                | FStar_Errors.Error (uu____71686,msg,uu____71688) ->
                    let uu____71691 = tts e2 t  in
                    let uu____71693 =
                      let uu____71695 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____71695
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____71691 uu____71693 msg))
  
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
  fun uu____71729  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___1127_71748 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___1127_71748.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___1127_71748.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___1127_71748.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___1127_71748.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___1127_71748.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___1127_71748.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___1127_71748.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___1127_71748.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___1127_71748.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___1127_71748.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___1127_71748.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___1127_71748.FStar_Tactics_Types.local_state)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____71773 = get_guard_policy ()  in
      bind uu____71773
        (fun old_pol  ->
           let uu____71779 = set_guard_policy pol  in
           bind uu____71779
             (fun uu____71783  ->
                bind t
                  (fun r  ->
                     let uu____71787 = set_guard_policy old_pol  in
                     bind uu____71787 (fun uu____71791  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____71795 = let uu____71800 = cur_goal ()  in trytac uu____71800  in
  bind uu____71795
    (fun uu___609_71807  ->
       match uu___609_71807 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____71813 = FStar_Options.peek ()  in ret uu____71813)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        mlog
          (fun uu____71838  ->
             let uu____71839 = FStar_TypeChecker_Rel.guard_to_string e g  in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason
               uu____71839)
          (fun uu____71844  ->
             let uu____71845 =
               add_implicits g.FStar_TypeChecker_Env.implicits  in
             bind uu____71845
               (fun uu____71849  ->
                  bind getopts
                    (fun opts  ->
                       let uu____71853 =
                         let uu____71854 =
                           FStar_TypeChecker_Rel.simplify_guard e g  in
                         uu____71854.FStar_TypeChecker_Env.guard_f  in
                       match uu____71853 with
                       | FStar_TypeChecker_Common.Trivial  -> ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____71858 = istrivial e f  in
                           if uu____71858
                           then ret ()
                           else
                             bind get
                               (fun ps  ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop  ->
                                      ((let uu____71871 =
                                          let uu____71877 =
                                            let uu____71879 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g
                                               in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____71879
                                             in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____71877)
                                           in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____71871);
                                       ret ())
                                  | FStar_Tactics_Types.Goal  ->
                                      mlog
                                        (fun uu____71885  ->
                                           let uu____71886 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____71886)
                                        (fun uu____71891  ->
                                           let uu____71892 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____71892
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___1156_71900 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___1156_71900.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___1156_71900.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___1156_71900.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___1156_71900.FStar_Tactics_Types.label)
                                                  }  in
                                                push_goals [goal1]))
                                  | FStar_Tactics_Types.SMT  ->
                                      mlog
                                        (fun uu____71904  ->
                                           let uu____71905 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____71905)
                                        (fun uu____71910  ->
                                           let uu____71911 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____71911
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___1163_71919 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___1163_71919.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___1163_71919.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___1163_71919.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___1163_71919.FStar_Tactics_Types.label)
                                                  }  in
                                                push_smt_goals [goal1]))
                                  | FStar_Tactics_Types.Force  ->
                                      mlog
                                        (fun uu____71923  ->
                                           let uu____71924 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____71924)
                                        (fun uu____71928  ->
                                           try
                                             (fun uu___1170_71933  ->
                                                match () with
                                                | () ->
                                                    let uu____71936 =
                                                      let uu____71938 =
                                                        let uu____71940 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____71940
                                                         in
                                                      Prims.op_Negation
                                                        uu____71938
                                                       in
                                                    if uu____71936
                                                    then
                                                      mlog
                                                        (fun uu____71947  ->
                                                           let uu____71948 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g
                                                              in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____71948)
                                                        (fun uu____71952  ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else ret ()) ()
                                           with
                                           | uu___1169_71957 ->
                                               mlog
                                                 (fun uu____71962  ->
                                                    let uu____71963 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g
                                                       in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____71963)
                                                 (fun uu____71967  ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____71979 =
      let uu____71982 = cur_goal ()  in
      bind uu____71982
        (fun goal  ->
           let uu____71988 =
             let uu____71997 = FStar_Tactics_Types.goal_env goal  in
             __tc_lax uu____71997 t  in
           bind uu____71988
             (fun uu____72008  ->
                match uu____72008 with
                | (uu____72017,typ,uu____72019) -> ret typ))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____71979
  
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
            let uu____72059 = mk_irrelevant_goal reason env phi opts label1
               in
            bind uu____72059 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____72071  ->
    let uu____72074 = cur_goal ()  in
    bind uu____72074
      (fun goal  ->
         let uu____72080 =
           let uu____72082 = FStar_Tactics_Types.goal_env goal  in
           let uu____72083 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____72082 uu____72083  in
         if uu____72080
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____72089 =
              let uu____72091 = FStar_Tactics_Types.goal_env goal  in
              let uu____72092 = FStar_Tactics_Types.goal_type goal  in
              tts uu____72091 uu____72092  in
            fail1 "Not a trivial goal: %s" uu____72089))
  
let divide : 'a 'b . FStar_BigInt.t -> 'a tac -> 'b tac -> ('a * 'b) tac =
  fun n1  ->
    fun l  ->
      fun r  ->
        bind get
          (fun p  ->
             let uu____72143 =
               try
                 (fun uu___1226_72166  ->
                    match () with
                    | () ->
                        let uu____72177 =
                          let uu____72186 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____72186
                            p.FStar_Tactics_Types.goals
                           in
                        ret uu____72177) ()
               with | uu___1225_72197 -> fail "divide: not enough goals"  in
             bind uu____72143
               (fun uu____72234  ->
                  match uu____72234 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___1208_72260 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___1208_72260.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___1208_72260.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___1208_72260.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___1208_72260.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___1208_72260.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___1208_72260.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___1208_72260.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___1208_72260.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___1208_72260.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___1208_72260.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___1208_72260.FStar_Tactics_Types.local_state)
                        }  in
                      let uu____72261 = set lp  in
                      bind uu____72261
                        (fun uu____72269  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___1214_72285 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___1214_72285.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___1214_72285.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___1214_72285.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___1214_72285.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___1214_72285.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___1214_72285.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___1214_72285.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___1214_72285.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___1214_72285.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___1214_72285.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___1214_72285.FStar_Tactics_Types.local_state)
                                       }  in
                                     let uu____72286 = set rp  in
                                     bind uu____72286
                                       (fun uu____72294  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___1220_72310 =
                                                        rp'  in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___1220_72310.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___1220_72310.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___1220_72310.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___1220_72310.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___1220_72310.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___1220_72310.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___1220_72310.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___1220_72310.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___1220_72310.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___1220_72310.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___1220_72310.FStar_Tactics_Types.local_state)
                                                      }  in
                                                    let uu____72311 = set p'
                                                       in
                                                    bind uu____72311
                                                      (fun uu____72319  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____72325 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____72347 = divide FStar_BigInt.one f idtac  in
    bind uu____72347
      (fun uu____72360  -> match uu____72360 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____72398::uu____72399 ->
             let uu____72402 =
               let uu____72411 = map tau  in
               divide FStar_BigInt.one tau uu____72411  in
             bind uu____72402
               (fun uu____72429  ->
                  match uu____72429 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____72471 =
        bind t1
          (fun uu____72476  ->
             let uu____72477 = map t2  in
             bind uu____72477 (fun uu____72485  -> ret ()))
         in
      focus uu____72471
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____72495  ->
    let uu____72498 =
      let uu____72501 = cur_goal ()  in
      bind uu____72501
        (fun goal  ->
           let uu____72510 =
             let uu____72517 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____72517  in
           match uu____72510 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____72526 =
                 let uu____72528 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____72528  in
               if uu____72526
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____72537 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____72537 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____72551 = new_uvar "intro" env' typ'  in
                  bind uu____72551
                    (fun uu____72568  ->
                       match uu____72568 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c))
                              in
                           let uu____72592 = set_solution goal sol  in
                           bind uu____72592
                             (fun uu____72598  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                    goal.FStar_Tactics_Types.label
                                   in
                                let uu____72600 =
                                  let uu____72603 = bnorm_goal g  in
                                  replace_cur uu____72603  in
                                bind uu____72600 (fun uu____72605  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____72610 =
                 let uu____72612 = FStar_Tactics_Types.goal_env goal  in
                 let uu____72613 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____72612 uu____72613  in
               fail1 "goal is not an arrow (%s)" uu____72610)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____72498
  
let (intro_rec :
  unit -> (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder) tac) =
  fun uu____72631  ->
    let uu____72638 = cur_goal ()  in
    bind uu____72638
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____72657 =
            let uu____72664 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____72664  in
          match uu____72657 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____72677 =
                let uu____72679 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____72679  in
              if uu____72677
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____72696 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____72696
                    in
                 let bs =
                   let uu____72707 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____72707; b]  in
                 let env' =
                   let uu____72733 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____72733 bs  in
                 let uu____72734 =
                   let uu____72741 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____72741  in
                 bind uu____72734
                   (fun uu____72761  ->
                      match uu____72761 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____72775 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____72778 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____72775
                              FStar_Parser_Const.effect_Tot_lid uu____72778
                              [] FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____72796 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____72796 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____72818 =
                                   let uu____72819 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____72819.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____72818
                                  in
                               let uu____72835 = set_solution goal tm  in
                               bind uu____72835
                                 (fun uu____72844  ->
                                    let uu____72845 =
                                      let uu____72848 =
                                        bnorm_goal
                                          (let uu___1291_72851 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___1291_72851.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___1291_72851.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___1291_72851.FStar_Tactics_Types.is_guard);
                                             FStar_Tactics_Types.label =
                                               (uu___1291_72851.FStar_Tactics_Types.label)
                                           })
                                         in
                                      replace_cur uu____72848  in
                                    bind uu____72845
                                      (fun uu____72858  ->
                                         let uu____72859 =
                                           let uu____72864 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____72864, b)  in
                                         ret uu____72859)))))
          | FStar_Pervasives_Native.None  ->
              let uu____72873 =
                let uu____72875 = FStar_Tactics_Types.goal_env goal  in
                let uu____72876 = FStar_Tactics_Types.goal_type goal  in
                tts uu____72875 uu____72876  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____72873))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____72896 = cur_goal ()  in
    bind uu____72896
      (fun goal  ->
         mlog
           (fun uu____72903  ->
              let uu____72904 =
                let uu____72906 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____72906  in
              FStar_Util.print1 "norm: witness = %s\n" uu____72904)
           (fun uu____72912  ->
              let steps =
                let uu____72916 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____72916
                 in
              let t =
                let uu____72920 = FStar_Tactics_Types.goal_env goal  in
                let uu____72921 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____72920 uu____72921  in
              let uu____72922 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____72922))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____72947 =
          bind get
            (fun ps  ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
                 | g::uu____72955 -> g.FStar_Tactics_Types.opts
                 | uu____72958 -> FStar_Options.peek ()  in
               mlog
                 (fun uu____72963  ->
                    let uu____72964 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____72964)
                 (fun uu____72969  ->
                    let uu____72970 = __tc_lax e t  in
                    bind uu____72970
                      (fun uu____72991  ->
                         match uu____72991 with
                         | (t1,uu____73001,uu____73002) ->
                             let steps =
                               let uu____73006 =
                                 FStar_TypeChecker_Normalize.tr_norm_steps s
                                  in
                               FStar_List.append
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu____73006
                                in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1
                                in
                             mlog
                               (fun uu____73012  ->
                                  let uu____73013 =
                                    FStar_Syntax_Print.term_to_string t2  in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____73013)
                               (fun uu____73017  -> ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____72947
  
let (refine_intro : unit -> unit tac) =
  fun uu____73030  ->
    let uu____73033 =
      let uu____73036 = cur_goal ()  in
      bind uu____73036
        (fun g  ->
           let uu____73043 =
             let uu____73054 = FStar_Tactics_Types.goal_env g  in
             let uu____73055 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____73054
               uu____73055
              in
           match uu____73043 with
           | (uu____73058,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____73084 =
                 let uu____73089 =
                   let uu____73094 =
                     let uu____73095 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____73095]  in
                   FStar_Syntax_Subst.open_term uu____73094 phi  in
                 match uu____73089 with
                 | (bvs,phi1) ->
                     let uu____73120 =
                       let uu____73121 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____73121  in
                     (uu____73120, phi1)
                  in
               (match uu____73084 with
                | (bv1,phi1) ->
                    let uu____73140 =
                      let uu____73143 = FStar_Tactics_Types.goal_env g  in
                      let uu____73144 =
                        let uu____73145 =
                          let uu____73148 =
                            let uu____73149 =
                              let uu____73156 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____73156)  in
                            FStar_Syntax_Syntax.NT uu____73149  in
                          [uu____73148]  in
                        FStar_Syntax_Subst.subst uu____73145 phi1  in
                      mk_irrelevant_goal "refine_intro refinement"
                        uu____73143 uu____73144 g.FStar_Tactics_Types.opts
                        g.FStar_Tactics_Types.label
                       in
                    bind uu____73140
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____73165  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____73033
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____73188 = cur_goal ()  in
      bind uu____73188
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____73197 = FStar_Tactics_Types.goal_env goal  in
               let uu____73198 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____73197 uu____73198
             else FStar_Tactics_Types.goal_env goal  in
           let uu____73201 = __tc env t  in
           bind uu____73201
             (fun uu____73220  ->
                match uu____73220 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____73235  ->
                         let uu____73236 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____73238 =
                           let uu____73240 =
                             FStar_Tactics_Types.goal_env goal  in
                           FStar_TypeChecker_Rel.guard_to_string uu____73240
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____73236 uu____73238)
                      (fun uu____73244  ->
                         let uu____73245 =
                           let uu____73248 =
                             FStar_Tactics_Types.goal_env goal  in
                           proc_guard "__exact typing" uu____73248 guard  in
                         bind uu____73245
                           (fun uu____73251  ->
                              mlog
                                (fun uu____73255  ->
                                   let uu____73256 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____73258 =
                                     let uu____73260 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____73260
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____73256 uu____73258)
                                (fun uu____73264  ->
                                   let uu____73265 =
                                     let uu____73269 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____73270 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____73269 typ uu____73270  in
                                   bind uu____73265
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____73280 =
                                             let uu____73282 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____73282 t1  in
                                           let uu____73283 =
                                             let uu____73285 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____73285 typ  in
                                           let uu____73286 =
                                             let uu____73288 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____73289 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____73288 uu____73289  in
                                           let uu____73290 =
                                             let uu____73292 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____73293 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____73292 uu____73293  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____73280 uu____73283
                                             uu____73286 uu____73290)))))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun try_refine  ->
    fun set_expected_typ1  ->
      fun tm  ->
        let uu____73319 =
          mlog
            (fun uu____73324  ->
               let uu____73325 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____73325)
            (fun uu____73330  ->
               let uu____73331 =
                 let uu____73338 = __exact_now set_expected_typ1 tm  in
                 catch uu____73338  in
               bind uu____73331
                 (fun uu___611_73347  ->
                    match uu___611_73347 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        traise e
                    | FStar_Util.Inl e ->
                        mlog
                          (fun uu____73358  ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____73362  ->
                             let uu____73363 =
                               let uu____73370 =
                                 let uu____73373 =
                                   norm [FStar_Syntax_Embeddings.Delta]  in
                                 bind uu____73373
                                   (fun uu____73378  ->
                                      let uu____73379 = refine_intro ()  in
                                      bind uu____73379
                                        (fun uu____73383  ->
                                           __exact_now set_expected_typ1 tm))
                                  in
                               catch uu____73370  in
                             bind uu____73363
                               (fun uu___610_73390  ->
                                  match uu___610_73390 with
                                  | FStar_Util.Inr r ->
                                      mlog
                                        (fun uu____73399  ->
                                           FStar_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu____73402  -> ret ())
                                  | FStar_Util.Inl uu____73403 ->
                                      mlog
                                        (fun uu____73405  ->
                                           FStar_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu____73408  -> traise e)))))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____73319
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____73460 = f x  in
          bind uu____73460
            (fun y  ->
               let uu____73468 = mapM f xs  in
               bind uu____73468 (fun ys  -> ret (y :: ys)))
  
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
          let uu____73540 = do_unify e ty1 ty2  in
          bind uu____73540
            (fun uu___612_73554  ->
               if uu___612_73554
               then ret acc
               else
                 (let uu____73574 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____73574 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____73595 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____73597 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____73595
                        uu____73597
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____73614 =
                        let uu____73616 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____73616  in
                      if uu____73614
                      then fail "Codomain is effectful"
                      else
                        (let uu____73640 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____73640
                           (fun uu____73667  ->
                              match uu____73667 with
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
      let uu____73757 =
        mlog
          (fun uu____73762  ->
             let uu____73763 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_apply: tm = %s\n" uu____73763)
          (fun uu____73768  ->
             let uu____73769 = cur_goal ()  in
             bind uu____73769
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____73777 = __tc e tm  in
                  bind uu____73777
                    (fun uu____73798  ->
                       match uu____73798 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____73811 =
                             let uu____73822 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____73822  in
                           bind uu____73811
                             (fun uvs  ->
                                let fix_qual q =
                                  match q with
                                  | FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Meta uu____73860)
                                      ->
                                      FStar_Pervasives_Native.Some
                                        (FStar_Syntax_Syntax.Implicit false)
                                  | uu____73864 -> q  in
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____73887  ->
                                       fun w  ->
                                         match uu____73887 with
                                         | (uvt,q,uu____73905) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, (fix_qual q))]) uvs tm1
                                   in
                                let uvset =
                                  let uu____73937 =
                                    FStar_Syntax_Free.new_uv_set ()  in
                                  FStar_List.fold_right
                                    (fun uu____73954  ->
                                       fun s  ->
                                         match uu____73954 with
                                         | (uu____73966,uu____73967,uv) ->
                                             let uu____73969 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                in
                                             FStar_Util.set_union s
                                               uu____73969) uvs uu____73937
                                   in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset  in
                                let uu____73979 = solve' goal w  in
                                bind uu____73979
                                  (fun uu____73984  ->
                                     let uu____73985 =
                                       mapM
                                         (fun uu____74002  ->
                                            match uu____74002 with
                                            | (uvt,q,uv) ->
                                                let uu____74014 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                   in
                                                (match uu____74014 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____74019 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____74020 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv)
                                                        in
                                                     if uu____74020
                                                     then ret ()
                                                     else
                                                       (let uu____74027 =
                                                          let uu____74030 =
                                                            bnorm_goal
                                                              (let uu___1452_74033
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___1452_74033.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___1452_74033.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false;
                                                                 FStar_Tactics_Types.label
                                                                   =
                                                                   (uu___1452_74033.FStar_Tactics_Types.label)
                                                               })
                                                             in
                                                          [uu____74030]  in
                                                        add_goals uu____74027)))
                                         uvs
                                        in
                                     bind uu____73985
                                       (fun uu____74038  ->
                                          proc_guard "apply guard" e guard))))))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____73757
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____74066 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____74066
    then
      let uu____74075 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____74090 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____74143 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____74075 with
      | (pre,post) ->
          let post1 =
            let uu____74176 =
              let uu____74187 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____74187]  in
            FStar_Syntax_Util.mk_app post uu____74176  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____74218 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____74218
       then
         let uu____74227 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____74227
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
            let uu____74306 = f x e  in
            bind uu____74306 (fun e'  -> fold_left f e' xs1)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____74321 =
      let uu____74324 =
        bind get
          (fun ps  ->
             mlog
               (fun uu____74331  ->
                  let uu____74332 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____74332)
               (fun uu____74338  ->
                  let is_unit_t t =
                    let uu____74346 =
                      let uu____74347 = FStar_Syntax_Subst.compress t  in
                      uu____74347.FStar_Syntax_Syntax.n  in
                    match uu____74346 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____74353 -> false  in
                  let uu____74355 = cur_goal ()  in
                  bind uu____74355
                    (fun goal  ->
                       let uu____74361 =
                         let uu____74370 = FStar_Tactics_Types.goal_env goal
                            in
                         __tc uu____74370 tm  in
                       bind uu____74361
                         (fun uu____74385  ->
                            match uu____74385 with
                            | (tm1,t,guard) ->
                                let uu____74397 =
                                  FStar_Syntax_Util.arrow_formals_comp t  in
                                (match uu____74397 with
                                 | (bs,comp) ->
                                     let uu____74430 = lemma_or_sq comp  in
                                     (match uu____74430 with
                                      | FStar_Pervasives_Native.None  ->
                                          fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre,post) ->
                                          let uu____74450 =
                                            fold_left
                                              (fun uu____74512  ->
                                                 fun uu____74513  ->
                                                   match (uu____74512,
                                                           uu____74513)
                                                   with
                                                   | ((b,aq),(uvs,imps,subst1))
                                                       ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst1
                                                           b.FStar_Syntax_Syntax.sort
                                                          in
                                                       let uu____74664 =
                                                         is_unit_t b_t  in
                                                       if uu____74664
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
                                                         (let uu____74787 =
                                                            let uu____74794 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            new_uvar
                                                              "apply_lemma"
                                                              uu____74794 b_t
                                                             in
                                                          bind uu____74787
                                                            (fun uu____74825 
                                                               ->
                                                               match uu____74825
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
                                          bind uu____74450
                                            (fun uu____75011  ->
                                               match uu____75011 with
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
                                                   let uu____75099 =
                                                     let uu____75103 =
                                                       FStar_Tactics_Types.goal_env
                                                         goal
                                                        in
                                                     let uu____75104 =
                                                       FStar_Syntax_Util.mk_squash
                                                         FStar_Syntax_Syntax.U_zero
                                                         post1
                                                        in
                                                     let uu____75105 =
                                                       FStar_Tactics_Types.goal_type
                                                         goal
                                                        in
                                                     do_unify uu____75103
                                                       uu____75104
                                                       uu____75105
                                                      in
                                                   bind uu____75099
                                                     (fun b  ->
                                                        if
                                                          Prims.op_Negation b
                                                        then
                                                          let uu____75116 =
                                                            let uu____75118 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            tts uu____75118
                                                              tm1
                                                             in
                                                          let uu____75119 =
                                                            let uu____75121 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            let uu____75122 =
                                                              FStar_Syntax_Util.mk_squash
                                                                FStar_Syntax_Syntax.U_zero
                                                                post1
                                                               in
                                                            tts uu____75121
                                                              uu____75122
                                                             in
                                                          let uu____75123 =
                                                            let uu____75125 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            let uu____75126 =
                                                              FStar_Tactics_Types.goal_type
                                                                goal
                                                               in
                                                            tts uu____75125
                                                              uu____75126
                                                             in
                                                          fail3
                                                            "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                            uu____75116
                                                            uu____75119
                                                            uu____75123
                                                        else
                                                          (let uu____75130 =
                                                             solve' goal
                                                               FStar_Syntax_Util.exp_unit
                                                              in
                                                           bind uu____75130
                                                             (fun uu____75138
                                                                 ->
                                                                let is_free_uvar
                                                                  uv t1 =
                                                                  let free_uvars
                                                                    =
                                                                    let uu____75164
                                                                    =
                                                                    let uu____75167
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____75167
                                                                     in
                                                                    FStar_List.map
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____75164
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
                                                                    let uu____75203
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____75203)
                                                                    goals
                                                                   in
                                                                let checkone
                                                                  t1 goals =
                                                                  let uu____75220
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                  match uu____75220
                                                                  with
                                                                  | (hd1,uu____75239)
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____75266)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____75283
                                                                    -> false)
                                                                   in
                                                                let uu____75285
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
                                                                    let uu____75328
                                                                    = imp  in
                                                                    match uu____75328
                                                                    with
                                                                    | 
                                                                    (term,ctx_uvar)
                                                                    ->
                                                                    let uu____75339
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____75339
                                                                    with
                                                                    | 
                                                                    (hd1,uu____75361)
                                                                    ->
                                                                    let uu____75386
                                                                    =
                                                                    let uu____75387
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____75387.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____75386
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____75395)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___1562_75415
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___1562_75415.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___1562_75415.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___1562_75415.FStar_Tactics_Types.is_guard);
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___1562_75415.FStar_Tactics_Types.label)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____75418
                                                                    ->
                                                                    mlog
                                                                    (fun
                                                                    uu____75424
                                                                     ->
                                                                    let uu____75425
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                                                     in
                                                                    let uu____75427
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____75425
                                                                    uu____75427)
                                                                    (fun
                                                                    uu____75434
                                                                     ->
                                                                    let env =
                                                                    let uu___1567_75436
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___1567_75436.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1567_75436.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1567_75436.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___1567_75436.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1567_75436.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1567_75436.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1567_75436.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1567_75436.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___1567_75436.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___1567_75436.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___1567_75436.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1567_75436.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1567_75436.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1567_75436.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1567_75436.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1567_75436.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1567_75436.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1567_75436.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___1567_75436.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___1567_75436.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___1567_75436.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1567_75436.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1567_75436.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1567_75436.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1567_75436.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1567_75436.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1567_75436.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1567_75436.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1567_75436.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1567_75436.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1567_75436.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1567_75436.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1567_75436.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1567_75436.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___1567_75436.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1567_75436.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1567_75436.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___1567_75436.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1567_75436.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1567_75436.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1567_75436.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1567_75436.FStar_TypeChecker_Env.nbe)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let uu____75439
                                                                    =
                                                                    let uu____75442
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____75446
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
                                                                    let uu____75448
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____75446
                                                                    uu____75448
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____75454
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    uu____75442
                                                                    uu____75454
                                                                    g_typ  in
                                                                    bind
                                                                    uu____75439
                                                                    (fun
                                                                    uu____75458
                                                                     ->
                                                                    ret []))))))
                                                                   in
                                                                bind
                                                                  uu____75285
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
                                                                    let uu____75522
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____75522
                                                                    then
                                                                    let uu____75527
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____75527
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
                                                                    let uu____75542
                                                                    =
                                                                    let uu____75544
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____75544
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____75542)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____75545
                                                                    =
                                                                    let uu____75548
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____75548
                                                                    guard  in
                                                                    bind
                                                                    uu____75545
                                                                    (fun
                                                                    uu____75552
                                                                     ->
                                                                    let uu____75553
                                                                    =
                                                                    let uu____75556
                                                                    =
                                                                    let uu____75558
                                                                    =
                                                                    let uu____75560
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____75561
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____75560
                                                                    uu____75561
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____75558
                                                                     in
                                                                    if
                                                                    uu____75556
                                                                    then
                                                                    let uu____75565
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____75565
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    goal.FStar_Tactics_Types.label
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____75553
                                                                    (fun
                                                                    uu____75570
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2)))))))))))))
         in
      focus uu____74324  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____74321
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____75594 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____75594 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____75604::(e1,uu____75606)::(e2,uu____75608)::[])) when
        (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) ||
          (FStar_Ident.lid_equals l FStar_Parser_Const.c_eq2_lid)
        -> FStar_Pervasives_Native.Some (e1, e2)
    | uu____75669 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____75694 = destruct_eq' typ  in
    match uu____75694 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____75724 = FStar_Syntax_Util.un_squash typ  in
        (match uu____75724 with
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
        let uu____75793 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____75793 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', bv', [])
            else
              (let uu____75851 = aux e'  in
               FStar_Util.map_opt uu____75851
                 (fun uu____75882  ->
                    match uu____75882 with
                    | (e'',bv,bvs) -> (e'', bv, (bv' :: bvs))))
         in
      let uu____75908 = aux e  in
      FStar_Util.map_opt uu____75908
        (fun uu____75939  ->
           match uu____75939 with
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
          let uu____76013 =
            let uu____76024 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____76024  in
          FStar_Util.map_opt uu____76013
            (fun uu____76042  ->
               match uu____76042 with
               | (e0,b11,bvs) ->
                   let s1 bv =
                     let uu___1640_76064 = bv  in
                     let uu____76065 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___1640_76064.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___1640_76064.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____76065
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___1644_76073 =
                       g.FStar_Tactics_Types.goal_ctx_uvar  in
                     let uu____76074 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____76083 =
                       let uu____76086 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____76086  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___1644_76073.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____76074;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____76083;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___1644_76073.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___1644_76073.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___1644_76073.FStar_Syntax_Syntax.ctx_uvar_range);
                       FStar_Syntax_Syntax.ctx_uvar_meta =
                         (uu___1644_76073.FStar_Syntax_Syntax.ctx_uvar_meta)
                     }  in
                   let uu___1647_76087 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1647_76087.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___1647_76087.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___1647_76087.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1647_76087.FStar_Tactics_Types.label)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____76098 =
      let uu____76101 = cur_goal ()  in
      bind uu____76101
        (fun goal  ->
           let uu____76109 = h  in
           match uu____76109 with
           | (bv,uu____76113) ->
               mlog
                 (fun uu____76121  ->
                    let uu____76122 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____76124 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____76122
                      uu____76124)
                 (fun uu____76129  ->
                    let uu____76130 =
                      let uu____76141 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____76141  in
                    match uu____76130 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                        let uu____76168 =
                          destruct_eq bv1.FStar_Syntax_Syntax.sort  in
                        (match uu____76168 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____76183 =
                               let uu____76184 =
                                 FStar_Syntax_Subst.compress x  in
                               uu____76184.FStar_Syntax_Syntax.n  in
                             (match uu____76183 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv2 =
                                    let uu___1670_76201 = bv2  in
                                    let uu____76202 =
                                      FStar_Syntax_Subst.subst s
                                        bv2.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1670_76201.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1670_76201.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____76202
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv1 :: bvs1)  in
                                  let new_goal =
                                    let uu___1674_76210 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____76211 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____76220 =
                                      let uu____76223 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____76223
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___1674_76210.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____76211;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____76220;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___1674_76210.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___1674_76210.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___1674_76210.FStar_Syntax_Syntax.ctx_uvar_range);
                                      FStar_Syntax_Syntax.ctx_uvar_meta =
                                        (uu___1674_76210.FStar_Syntax_Syntax.ctx_uvar_meta)
                                    }  in
                                  replace_cur
                                    (let uu___1677_76226 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___1677_76226.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___1677_76226.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___1677_76226.FStar_Tactics_Types.is_guard);
                                       FStar_Tactics_Types.label =
                                         (uu___1677_76226.FStar_Tactics_Types.label)
                                     })
                              | uu____76227 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____76229 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____76098
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____76259 =
        let uu____76262 = cur_goal ()  in
        bind uu____76262
          (fun goal  ->
             let uu____76273 = b  in
             match uu____76273 with
             | (bv,uu____76277) ->
                 let bv' =
                   let uu____76283 =
                     let uu___1688_76284 = bv  in
                     let uu____76285 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____76285;
                       FStar_Syntax_Syntax.index =
                         (uu___1688_76284.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___1688_76284.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____76283  in
                 let s1 =
                   let uu____76290 =
                     let uu____76291 =
                       let uu____76298 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____76298)  in
                     FStar_Syntax_Syntax.NT uu____76291  in
                   [uu____76290]  in
                 let uu____76303 = subst_goal bv bv' s1 goal  in
                 (match uu____76303 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____76259
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____76325 =
      let uu____76328 = cur_goal ()  in
      bind uu____76328
        (fun goal  ->
           let uu____76337 = b  in
           match uu____76337 with
           | (bv,uu____76341) ->
               let uu____76346 =
                 let uu____76357 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____76357  in
               (match uu____76346 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                    let uu____76384 = FStar_Syntax_Util.type_u ()  in
                    (match uu____76384 with
                     | (ty,u) ->
                         let uu____76393 = new_uvar "binder_retype" e0 ty  in
                         bind uu____76393
                           (fun uu____76412  ->
                              match uu____76412 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___1712_76422 = bv1  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1712_76422.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1712_76422.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____76426 =
                                      let uu____76427 =
                                        let uu____76434 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv1, uu____76434)  in
                                      FStar_Syntax_Syntax.NT uu____76427  in
                                    [uu____76426]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___1717_76446 = b1  in
                                         let uu____76447 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___1717_76446.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___1717_76446.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____76447
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____76454  ->
                                       let new_goal =
                                         let uu____76456 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____76457 =
                                           let uu____76458 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____76458
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____76456 uu____76457
                                          in
                                       let uu____76459 = add_goals [new_goal]
                                          in
                                       bind uu____76459
                                         (fun uu____76464  ->
                                            let uu____76465 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv1.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____76465
                                              goal.FStar_Tactics_Types.opts
                                              goal.FStar_Tactics_Types.label))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____76325
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____76491 =
        let uu____76494 = cur_goal ()  in
        bind uu____76494
          (fun goal  ->
             let uu____76503 = b  in
             match uu____76503 with
             | (bv,uu____76507) ->
                 let uu____76512 =
                   let uu____76523 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____76523  in
                 (match uu____76512 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                      let steps =
                        let uu____76553 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____76553
                         in
                      let sort' =
                        normalize steps e0 bv1.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___1738_76558 = bv1  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___1738_76558.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___1738_76558.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____76560 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____76560))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____76491
  
let (revert : unit -> unit tac) =
  fun uu____76573  ->
    let uu____76576 = cur_goal ()  in
    bind uu____76576
      (fun goal  ->
         let uu____76582 =
           let uu____76589 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____76589  in
         match uu____76582 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____76606 =
                 let uu____76609 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____76609  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____76606
                in
             let uu____76624 = new_uvar "revert" env' typ'  in
             bind uu____76624
               (fun uu____76640  ->
                  match uu____76640 with
                  | (r,u_r) ->
                      let uu____76649 =
                        let uu____76652 =
                          let uu____76653 =
                            let uu____76654 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____76654.FStar_Syntax_Syntax.pos  in
                          let uu____76657 =
                            let uu____76662 =
                              let uu____76663 =
                                let uu____76672 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____76672  in
                              [uu____76663]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____76662  in
                          uu____76657 FStar_Pervasives_Native.None
                            uu____76653
                           in
                        set_solution goal uu____76652  in
                      bind uu____76649
                        (fun uu____76693  ->
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
      let uu____76707 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____76707
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____76723 = cur_goal ()  in
    bind uu____76723
      (fun goal  ->
         mlog
           (fun uu____76731  ->
              let uu____76732 = FStar_Syntax_Print.binder_to_string b  in
              let uu____76734 =
                let uu____76736 =
                  let uu____76738 =
                    let uu____76747 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____76747  in
                  FStar_All.pipe_right uu____76738 FStar_List.length  in
                FStar_All.pipe_right uu____76736 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____76732 uu____76734)
           (fun uu____76768  ->
              let uu____76769 =
                let uu____76780 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____76780  in
              match uu____76769 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bv1,bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____76825 =
                          free_in bv1 bv'.FStar_Syntax_Syntax.sort  in
                        if uu____76825
                        then
                          let uu____76830 =
                            let uu____76832 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____76832
                             in
                          fail uu____76830
                        else check1 bvs2
                     in
                  let uu____76837 =
                    let uu____76839 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv1 uu____76839  in
                  if uu____76837
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____76846 = check1 bvs  in
                     bind uu____76846
                       (fun uu____76852  ->
                          let env' = push_bvs e' bvs  in
                          let uu____76854 =
                            let uu____76861 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____76861  in
                          bind uu____76854
                            (fun uu____76871  ->
                               match uu____76871 with
                               | (ut,uvar_ut) ->
                                   let uu____76880 = set_solution goal ut  in
                                   bind uu____76880
                                     (fun uu____76885  ->
                                        let uu____76886 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                            goal.FStar_Tactics_Types.label
                                           in
                                        replace_cur uu____76886))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____76894  ->
    let uu____76897 = cur_goal ()  in
    bind uu____76897
      (fun goal  ->
         let uu____76903 =
           let uu____76910 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____76910  in
         match uu____76903 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____76919) ->
             let uu____76924 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____76924)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____76937 = cur_goal ()  in
    bind uu____76937
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____76947 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____76947  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____76950  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____76963 = cur_goal ()  in
    bind uu____76963
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____76973 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____76973  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____76976  -> add_goals [g']))
  
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
            let uu____77017 = FStar_Syntax_Subst.compress t  in
            uu____77017.FStar_Syntax_Syntax.n  in
          let uu____77020 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___1922_77027 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___1922_77027.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___1922_77027.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____77020
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____77044 =
                   let uu____77045 = FStar_Syntax_Subst.compress t1  in
                   uu____77045.FStar_Syntax_Syntax.n  in
                 match uu____77044 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____77076 = ff hd1  in
                     bind uu____77076
                       (fun hd2  ->
                          let fa uu____77102 =
                            match uu____77102 with
                            | (a,q) ->
                                let uu____77123 = ff a  in
                                bind uu____77123 (fun a1  -> ret (a1, q))
                             in
                          let uu____77142 = mapM fa args  in
                          bind uu____77142
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____77224 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____77224 with
                      | (bs1,t') ->
                          let uu____77233 =
                            let uu____77236 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____77236 t'  in
                          bind uu____77233
                            (fun t''  ->
                               let uu____77240 =
                                 let uu____77241 =
                                   let uu____77260 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____77269 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____77260, uu____77269, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____77241  in
                               ret uu____77240))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____77344 = ff hd1  in
                     bind uu____77344
                       (fun hd2  ->
                          let ffb br =
                            let uu____77359 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____77359 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____77391 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____77391  in
                                let uu____77392 = ff1 e  in
                                bind uu____77392
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____77407 = mapM ffb brs  in
                          bind uu____77407
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____77451;
                          FStar_Syntax_Syntax.lbtyp = uu____77452;
                          FStar_Syntax_Syntax.lbeff = uu____77453;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____77455;
                          FStar_Syntax_Syntax.lbpos = uu____77456;_}::[]),e)
                     ->
                     let lb =
                       let uu____77484 =
                         let uu____77485 = FStar_Syntax_Subst.compress t1  in
                         uu____77485.FStar_Syntax_Syntax.n  in
                       match uu____77484 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____77489) -> lb
                       | uu____77505 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____77515 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____77515
                         (fun def1  ->
                            ret
                              (let uu___1875_77521 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1875_77521.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1875_77521.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1875_77521.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1875_77521.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1875_77521.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1875_77521.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____77522 = fflb lb  in
                     bind uu____77522
                       (fun lb1  ->
                          let uu____77532 =
                            let uu____77537 =
                              let uu____77538 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____77538]  in
                            FStar_Syntax_Subst.open_term uu____77537 e  in
                          match uu____77532 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____77568 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____77568  in
                              let uu____77569 = ff1 e1  in
                              bind uu____77569
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____77616 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____77616
                         (fun def  ->
                            ret
                              (let uu___1893_77622 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1893_77622.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1893_77622.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1893_77622.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1893_77622.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1893_77622.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1893_77622.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____77623 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____77623 with
                      | (lbs1,e1) ->
                          let uu____77638 = mapM fflb lbs1  in
                          bind uu____77638
                            (fun lbs2  ->
                               let uu____77650 = ff e1  in
                               bind uu____77650
                                 (fun e2  ->
                                    let uu____77658 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____77658 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____77729 = ff t2  in
                     bind uu____77729
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____77760 = ff t2  in
                     bind uu____77760
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____77767 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___1917_77774 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___1917_77774.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___1917_77774.FStar_Syntax_Syntax.vars)
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
              let uu____77821 =
                FStar_TypeChecker_TcTerm.tc_term
                  (let uu___1930_77830 = env  in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___1930_77830.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___1930_77830.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___1930_77830.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___1930_77830.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_sig =
                       (uu___1930_77830.FStar_TypeChecker_Env.gamma_sig);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___1930_77830.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___1930_77830.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___1930_77830.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___1930_77830.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.attrtab =
                       (uu___1930_77830.FStar_TypeChecker_Env.attrtab);
                     FStar_TypeChecker_Env.is_pattern =
                       (uu___1930_77830.FStar_TypeChecker_Env.is_pattern);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___1930_77830.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___1930_77830.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___1930_77830.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___1930_77830.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___1930_77830.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___1930_77830.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___1930_77830.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___1930_77830.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___1930_77830.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax = true;
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___1930_77830.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.phase1 =
                       (uu___1930_77830.FStar_TypeChecker_Env.phase1);
                     FStar_TypeChecker_Env.failhard =
                       (uu___1930_77830.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___1930_77830.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.uvar_subtyping =
                       (uu___1930_77830.FStar_TypeChecker_Env.uvar_subtyping);
                     FStar_TypeChecker_Env.tc_term =
                       (uu___1930_77830.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.type_of =
                       (uu___1930_77830.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___1930_77830.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.check_type_of =
                       (uu___1930_77830.FStar_TypeChecker_Env.check_type_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___1930_77830.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (uu___1930_77830.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (uu___1930_77830.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.fv_delta_depths =
                       (uu___1930_77830.FStar_TypeChecker_Env.fv_delta_depths);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___1930_77830.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (uu___1930_77830.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.splice =
                       (uu___1930_77830.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.postprocess =
                       (uu___1930_77830.FStar_TypeChecker_Env.postprocess);
                     FStar_TypeChecker_Env.is_native_tactic =
                       (uu___1930_77830.FStar_TypeChecker_Env.is_native_tactic);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___1930_77830.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (uu___1930_77830.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (uu___1930_77830.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.nbe =
                       (uu___1930_77830.FStar_TypeChecker_Env.nbe)
                   }) t
                 in
              match uu____77821 with
              | (t1,lcomp,g) ->
                  let uu____77837 =
                    (let uu____77841 =
                       FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                     Prims.op_Negation uu____77841) ||
                      (let uu____77844 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____77844)
                     in
                  if uu____77837
                  then ret t1
                  else
                    (let rewrite_eq =
                       let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                       let uu____77855 = new_uvar "pointwise_rec" env typ  in
                       bind uu____77855
                         (fun uu____77872  ->
                            match uu____77872 with
                            | (ut,uvar_ut) ->
                                (log ps
                                   (fun uu____77885  ->
                                      let uu____77886 =
                                        FStar_Syntax_Print.term_to_string t1
                                         in
                                      let uu____77888 =
                                        FStar_Syntax_Print.term_to_string ut
                                         in
                                      FStar_Util.print2
                                        "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                        uu____77886 uu____77888);
                                 (let uu____77891 =
                                    let uu____77894 =
                                      let uu____77895 =
                                        FStar_TypeChecker_TcTerm.universe_of
                                          env typ
                                         in
                                      FStar_Syntax_Util.mk_eq2 uu____77895
                                        typ t1 ut
                                       in
                                    add_irrelevant_goal
                                      "pointwise_rec equation" env
                                      uu____77894 opts label1
                                     in
                                  bind uu____77891
                                    (fun uu____77899  ->
                                       let uu____77900 =
                                         bind tau
                                           (fun uu____77906  ->
                                              let ut1 =
                                                FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                  env ut
                                                 in
                                              log ps
                                                (fun uu____77912  ->
                                                   let uu____77913 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1
                                                      in
                                                   let uu____77915 =
                                                     FStar_Syntax_Print.term_to_string
                                                       ut1
                                                      in
                                                   FStar_Util.print2
                                                     "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                     uu____77913 uu____77915);
                                              ret ut1)
                                          in
                                       focus uu____77900))))
                        in
                     let uu____77918 = catch rewrite_eq  in
                     bind uu____77918
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
          let uu____78136 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____78136
            (fun t1  ->
               let uu____78144 =
                 f env
                   (let uu___2007_78153 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___2007_78153.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___2007_78153.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____78144
                 (fun uu____78169  ->
                    match uu____78169 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____78192 =
                               let uu____78193 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____78193.FStar_Syntax_Syntax.n  in
                             match uu____78192 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____78230 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____78230
                                   (fun uu____78255  ->
                                      match uu____78255 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____78271 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____78271
                                            (fun uu____78298  ->
                                               match uu____78298 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___1987_78328 =
                                                         t3  in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___1987_78328.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___1987_78328.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____78370 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____78370 with
                                  | (bs1,t') ->
                                      let uu____78385 =
                                        let uu____78392 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____78392 ctrl1 t'
                                         in
                                      bind uu____78385
                                        (fun uu____78410  ->
                                           match uu____78410 with
                                           | (t'',ctrl2) ->
                                               let uu____78425 =
                                                 let uu____78432 =
                                                   let uu___2000_78435 = t4
                                                      in
                                                   let uu____78438 =
                                                     let uu____78439 =
                                                       let uu____78458 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____78467 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____78458,
                                                         uu____78467, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____78439
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____78438;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___2000_78435.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___2000_78435.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____78432, ctrl2)  in
                                               ret uu____78425))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____78520 -> ret (t3, ctrl1))))

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
              let uu____78567 = ctrl_tac_fold f env ctrl t  in
              bind uu____78567
                (fun uu____78591  ->
                   match uu____78591 with
                   | (t1,ctrl1) ->
                       let uu____78606 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____78606
                         (fun uu____78633  ->
                            match uu____78633 with
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
                let uu____78727 =
                  let uu____78735 =
                    add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                      opts label1
                     in
                  bind uu____78735
                    (fun uu____78746  ->
                       let uu____78747 = ctrl t1  in
                       bind uu____78747
                         (fun res  ->
                            let uu____78774 = trivial ()  in
                            bind uu____78774 (fun uu____78783  -> ret res)))
                   in
                bind uu____78727
                  (fun uu____78801  ->
                     match uu____78801 with
                     | (should_rewrite,ctrl1) ->
                         if Prims.op_Negation should_rewrite
                         then ret (t1, ctrl1)
                         else
                           (let uu____78830 =
                              FStar_TypeChecker_TcTerm.tc_term
                                (let uu___2037_78839 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___2037_78839.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___2037_78839.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___2037_78839.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___2037_78839.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___2037_78839.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___2037_78839.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___2037_78839.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___2037_78839.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___2037_78839.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___2037_78839.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___2037_78839.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___2037_78839.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___2037_78839.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___2037_78839.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___2037_78839.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___2037_78839.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___2037_78839.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___2037_78839.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___2037_78839.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___2037_78839.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___2037_78839.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___2037_78839.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___2037_78839.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___2037_78839.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___2037_78839.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___2037_78839.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___2037_78839.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___2037_78839.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___2037_78839.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___2037_78839.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___2037_78839.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___2037_78839.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___2037_78839.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___2037_78839.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___2037_78839.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___2037_78839.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___2037_78839.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___2037_78839.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___2037_78839.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___2037_78839.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___2037_78839.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___2037_78839.FStar_TypeChecker_Env.nbe)
                                 }) t1
                               in
                            match uu____78830 with
                            | (t2,lcomp,g) ->
                                let uu____78850 =
                                  (let uu____78854 =
                                     FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                       lcomp
                                      in
                                   Prims.op_Negation uu____78854) ||
                                    (let uu____78857 =
                                       FStar_TypeChecker_Env.is_trivial g  in
                                     Prims.op_Negation uu____78857)
                                   in
                                if uu____78850
                                then ret (t2, globalStop)
                                else
                                  (let typ =
                                     lcomp.FStar_Syntax_Syntax.res_typ  in
                                   let uu____78873 =
                                     new_uvar "pointwise_rec" env typ  in
                                   bind uu____78873
                                     (fun uu____78894  ->
                                        match uu____78894 with
                                        | (ut,uvar_ut) ->
                                            (log ps
                                               (fun uu____78911  ->
                                                  let uu____78912 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t2
                                                     in
                                                  let uu____78914 =
                                                    FStar_Syntax_Print.term_to_string
                                                      ut
                                                     in
                                                  FStar_Util.print2
                                                    "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                    uu____78912 uu____78914);
                                             (let uu____78917 =
                                                let uu____78920 =
                                                  let uu____78921 =
                                                    FStar_TypeChecker_TcTerm.universe_of
                                                      env typ
                                                     in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____78921 typ t2 ut
                                                   in
                                                add_irrelevant_goal
                                                  "rewrite_rec equation" env
                                                  uu____78920 opts label1
                                                 in
                                              bind uu____78917
                                                (fun uu____78929  ->
                                                   let uu____78930 =
                                                     bind rewriter
                                                       (fun uu____78944  ->
                                                          let ut1 =
                                                            FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                              env ut
                                                             in
                                                          log ps
                                                            (fun uu____78950 
                                                               ->
                                                               let uu____78951
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   t2
                                                                  in
                                                               let uu____78953
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   ut1
                                                                  in
                                                               FStar_Util.print2
                                                                 "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                                 uu____78951
                                                                 uu____78953);
                                                          ret (ut1, ctrl1))
                                                      in
                                                   focus uu____78930)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term -> (Prims.bool * FStar_BigInt.t) tac) ->
    unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____78999 =
        bind get
          (fun ps  ->
             let uu____79009 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____79009 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____79047  ->
                       let uu____79048 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____79048);
                  bind dismiss_all
                    (fun uu____79053  ->
                       let uu____79054 =
                         let uu____79061 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____79061
                           keepGoing gt1
                          in
                       bind uu____79054
                         (fun uu____79073  ->
                            match uu____79073 with
                            | (gt',uu____79081) ->
                                (log ps
                                   (fun uu____79085  ->
                                      let uu____79086 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____79086);
                                 (let uu____79089 = push_goals gs  in
                                  bind uu____79089
                                    (fun uu____79094  ->
                                       let uu____79095 =
                                         let uu____79098 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____79098]  in
                                       add_goals uu____79095)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____78999
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____79123 =
        bind get
          (fun ps  ->
             let uu____79133 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____79133 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____79171  ->
                       let uu____79172 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____79172);
                  bind dismiss_all
                    (fun uu____79177  ->
                       let uu____79178 =
                         let uu____79181 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____79181 gt1
                          in
                       bind uu____79178
                         (fun gt'  ->
                            log ps
                              (fun uu____79189  ->
                                 let uu____79190 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____79190);
                            (let uu____79193 = push_goals gs  in
                             bind uu____79193
                               (fun uu____79198  ->
                                  let uu____79199 =
                                    let uu____79202 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____79202]  in
                                  add_goals uu____79199))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____79123
  
let (trefl : unit -> unit tac) =
  fun uu____79215  ->
    let uu____79218 =
      let uu____79221 = cur_goal ()  in
      bind uu____79221
        (fun g  ->
           let uu____79239 =
             let uu____79244 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____79244  in
           match uu____79239 with
           | FStar_Pervasives_Native.Some t ->
               let uu____79252 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____79252 with
                | (hd1,args) ->
                    let uu____79291 =
                      let uu____79304 =
                        let uu____79305 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____79305.FStar_Syntax_Syntax.n  in
                      (uu____79304, args)  in
                    (match uu____79291 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____79319::(l,uu____79321)::(r,uu____79323)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____79370 =
                           let uu____79374 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____79374 l r  in
                         bind uu____79370
                           (fun b  ->
                              if b
                              then solve' g FStar_Syntax_Util.exp_unit
                              else
                                (let l1 =
                                   let uu____79385 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____79385 l
                                    in
                                 let r1 =
                                   let uu____79387 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____79387 r
                                    in
                                 let uu____79388 =
                                   let uu____79392 =
                                     FStar_Tactics_Types.goal_env g  in
                                   do_unify uu____79392 l1 r1  in
                                 bind uu____79388
                                   (fun b1  ->
                                      if b1
                                      then
                                        solve' g FStar_Syntax_Util.exp_unit
                                      else
                                        (let uu____79402 =
                                           let uu____79404 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____79404 l1  in
                                         let uu____79405 =
                                           let uu____79407 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____79407 r1  in
                                         fail2
                                           "not a trivial equality ((%s) vs (%s))"
                                           uu____79402 uu____79405))))
                     | (hd2,uu____79410) ->
                         let uu____79427 =
                           let uu____79429 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____79429 t  in
                         fail1 "trefl: not an equality (%s)" uu____79427))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____79218
  
let (dup : unit -> unit tac) =
  fun uu____79446  ->
    let uu____79449 = cur_goal ()  in
    bind uu____79449
      (fun g  ->
         let uu____79455 =
           let uu____79462 = FStar_Tactics_Types.goal_env g  in
           let uu____79463 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____79462 uu____79463  in
         bind uu____79455
           (fun uu____79473  ->
              match uu____79473 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___2129_79483 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___2129_79483.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___2129_79483.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___2129_79483.FStar_Tactics_Types.is_guard);
                      FStar_Tactics_Types.label =
                        (uu___2129_79483.FStar_Tactics_Types.label)
                    }  in
                  bind __dismiss
                    (fun uu____79486  ->
                       let uu____79487 =
                         let uu____79490 = FStar_Tactics_Types.goal_env g  in
                         let uu____79491 =
                           let uu____79492 =
                             let uu____79493 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____79494 =
                               FStar_Tactics_Types.goal_type g  in
                             FStar_TypeChecker_TcTerm.universe_of uu____79493
                               uu____79494
                              in
                           let uu____79495 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____79496 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____79492 uu____79495 u
                             uu____79496
                            in
                         add_irrelevant_goal "dup equation" uu____79490
                           uu____79491 g.FStar_Tactics_Types.opts
                           g.FStar_Tactics_Types.label
                          in
                       bind uu____79487
                         (fun uu____79500  ->
                            let uu____79501 = add_goals [g']  in
                            bind uu____79501 (fun uu____79505  -> ret ())))))
  
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
              let uu____79631 = f x y  in
              if uu____79631 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____79654 -> (acc, l11, l21)  in
        let uu____79669 = aux [] l1 l2  in
        match uu____79669 with | (pr,t1,t2) -> ((FStar_List.rev pr), t1, t2)
  
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
      let uu____79775 = get_phi g1  in
      match uu____79775 with
      | FStar_Pervasives_Native.None  -> fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____79782 = get_phi g2  in
          (match uu____79782 with
           | FStar_Pervasives_Native.None  -> fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let uu____79795 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2)
                  in
               (match uu____79795 with
                | (gamma,r1,r2) ->
                    let t1 =
                      let uu____79826 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1)
                         in
                      close_forall_no_univs1 uu____79826 phi1  in
                    let t2 =
                      let uu____79836 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2)
                         in
                      close_forall_no_univs1 uu____79836 phi2  in
                    let uu____79845 =
                      set_solution g1 FStar_Syntax_Util.exp_unit  in
                    bind uu____79845
                      (fun uu____79850  ->
                         let uu____79851 =
                           set_solution g2 FStar_Syntax_Util.exp_unit  in
                         bind uu____79851
                           (fun uu____79858  ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2  in
                              let nenv =
                                let uu___2180_79863 =
                                  FStar_Tactics_Types.goal_env g1  in
                                let uu____79864 =
                                  FStar_Util.smap_create
                                    (Prims.parse_int "100")
                                   in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___2180_79863.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___2180_79863.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___2180_79863.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___2180_79863.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____79864;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___2180_79863.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___2180_79863.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___2180_79863.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___2180_79863.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___2180_79863.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___2180_79863.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___2180_79863.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___2180_79863.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___2180_79863.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___2180_79863.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___2180_79863.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___2180_79863.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___2180_79863.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___2180_79863.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___2180_79863.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___2180_79863.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___2180_79863.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___2180_79863.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___2180_79863.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___2180_79863.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___2180_79863.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___2180_79863.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___2180_79863.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___2180_79863.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___2180_79863.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___2180_79863.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___2180_79863.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___2180_79863.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___2180_79863.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___2180_79863.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___2180_79863.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___2180_79863.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___2180_79863.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___2180_79863.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___2180_79863.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___2180_79863.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___2180_79863.FStar_TypeChecker_Env.nbe)
                                }  in
                              let uu____79868 =
                                mk_irrelevant_goal "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                  g1.FStar_Tactics_Types.label
                                 in
                              bind uu____79868
                                (fun goal  ->
                                   mlog
                                     (fun uu____79878  ->
                                        let uu____79879 =
                                          goal_to_string_verbose g1  in
                                        let uu____79881 =
                                          goal_to_string_verbose g2  in
                                        let uu____79883 =
                                          goal_to_string_verbose goal  in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____79879 uu____79881 uu____79883)
                                     (fun uu____79887  -> ret goal))))))
  
let (join : unit -> unit tac) =
  fun uu____79895  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____79911 =
               set
                 (let uu___2195_79916 = ps  in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___2195_79916.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.main_goal =
                      (uu___2195_79916.FStar_Tactics_Types.main_goal);
                    FStar_Tactics_Types.all_implicits =
                      (uu___2195_79916.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___2195_79916.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___2195_79916.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___2195_79916.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___2195_79916.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___2195_79916.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___2195_79916.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___2195_79916.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___2195_79916.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___2195_79916.FStar_Tactics_Types.local_state)
                  })
                in
             bind uu____79911
               (fun uu____79919  ->
                  let uu____79920 = join_goals g1 g2  in
                  bind uu____79920 (fun g12  -> add_goals [g12]))
         | uu____79925 -> fail "join: less than 2 goals")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) tac)
  =
  fun t  ->
    let uu____79947 =
      let uu____79954 = cur_goal ()  in
      bind uu____79954
        (fun g  ->
           let uu____79964 =
             let uu____79973 = FStar_Tactics_Types.goal_env g  in
             __tc uu____79973 t  in
           bind uu____79964
             (fun uu____80001  ->
                match uu____80001 with
                | (t1,typ,guard) ->
                    let uu____80017 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____80017 with
                     | (hd1,args) ->
                         let uu____80066 =
                           let uu____80081 =
                             let uu____80082 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____80082.FStar_Syntax_Syntax.n  in
                           (uu____80081, args)  in
                         (match uu____80066 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____80103)::(q,uu____80105)::[]) when
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
                                let uu____80159 =
                                  let uu____80160 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____80160
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____80159
                                 in
                              let g2 =
                                let uu____80162 =
                                  let uu____80163 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____80163
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____80162
                                 in
                              bind __dismiss
                                (fun uu____80170  ->
                                   let uu____80171 = add_goals [g1; g2]  in
                                   bind uu____80171
                                     (fun uu____80180  ->
                                        let uu____80181 =
                                          let uu____80186 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____80187 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____80186, uu____80187)  in
                                        ret uu____80181))
                          | uu____80192 ->
                              let uu____80207 =
                                let uu____80209 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____80209 typ  in
                              fail1 "Not a disjunction: %s" uu____80207))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____79947
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____80244 =
      let uu____80247 = cur_goal ()  in
      bind uu____80247
        (fun g  ->
           FStar_Options.push ();
           (let uu____80260 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____80260);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___2232_80267 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___2232_80267.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___2232_80267.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___2232_80267.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___2232_80267.FStar_Tactics_Types.label)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____80244
  
let (top_env : unit -> env tac) =
  fun uu____80284  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____80299  ->
    let uu____80303 = cur_goal ()  in
    bind uu____80303
      (fun g  ->
         let uu____80310 =
           (FStar_Options.lax ()) ||
             (let uu____80313 = FStar_Tactics_Types.goal_env g  in
              uu____80313.FStar_TypeChecker_Env.lax)
            in
         ret uu____80310)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____80330 =
        mlog
          (fun uu____80335  ->
             let uu____80336 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____80336)
          (fun uu____80341  ->
             let uu____80342 = cur_goal ()  in
             bind uu____80342
               (fun goal  ->
                  let env =
                    let uu____80350 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____80350 ty  in
                  let uu____80351 = __tc_ghost env tm  in
                  bind uu____80351
                    (fun uu____80370  ->
                       match uu____80370 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____80384  ->
                                let uu____80385 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____80385)
                             (fun uu____80389  ->
                                mlog
                                  (fun uu____80392  ->
                                     let uu____80393 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____80393)
                                  (fun uu____80398  ->
                                     let uu____80399 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____80399
                                       (fun uu____80404  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____80330
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____80429 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____80435 =
              let uu____80442 =
                let uu____80443 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____80443
                 in
              new_uvar "uvar_env.2" env uu____80442  in
            bind uu____80435
              (fun uu____80460  ->
                 match uu____80460 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____80429
        (fun typ  ->
           let uu____80472 = new_uvar "uvar_env" env typ  in
           bind uu____80472
             (fun uu____80487  ->
                match uu____80487 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____80506 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____80525 -> g.FStar_Tactics_Types.opts
             | uu____80528 -> FStar_Options.peek ()  in
           let uu____80531 = FStar_Syntax_Util.head_and_args t  in
           match uu____80531 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____80551);
                FStar_Syntax_Syntax.pos = uu____80552;
                FStar_Syntax_Syntax.vars = uu____80553;_},uu____80554)
               ->
               let env1 =
                 let uu___2286_80596 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___2286_80596.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___2286_80596.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___2286_80596.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___2286_80596.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___2286_80596.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___2286_80596.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___2286_80596.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___2286_80596.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___2286_80596.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___2286_80596.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___2286_80596.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___2286_80596.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___2286_80596.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___2286_80596.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___2286_80596.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___2286_80596.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___2286_80596.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___2286_80596.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___2286_80596.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___2286_80596.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___2286_80596.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___2286_80596.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___2286_80596.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___2286_80596.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___2286_80596.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___2286_80596.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___2286_80596.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___2286_80596.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___2286_80596.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___2286_80596.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___2286_80596.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___2286_80596.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___2286_80596.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___2286_80596.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___2286_80596.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___2286_80596.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___2286_80596.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___2286_80596.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___2286_80596.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___2286_80596.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___2286_80596.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___2286_80596.FStar_TypeChecker_Env.nbe)
                 }  in
               let g =
                 FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false ""  in
               let uu____80600 =
                 let uu____80603 = bnorm_goal g  in [uu____80603]  in
               add_goals uu____80600
           | uu____80604 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____80506
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____80666 = if b then t2 else ret false  in
             bind uu____80666 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____80692 = trytac comp  in
      bind uu____80692
        (fun uu___613_80704  ->
           match uu___613_80704 with
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
        let uu____80746 =
          bind get
            (fun ps  ->
               let uu____80754 = __tc e t1  in
               bind uu____80754
                 (fun uu____80775  ->
                    match uu____80775 with
                    | (t11,ty1,g1) ->
                        let uu____80788 = __tc e t2  in
                        bind uu____80788
                          (fun uu____80809  ->
                             match uu____80809 with
                             | (t21,ty2,g2) ->
                                 let uu____80822 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____80822
                                   (fun uu____80829  ->
                                      let uu____80830 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____80830
                                        (fun uu____80838  ->
                                           let uu____80839 =
                                             do_unify e ty1 ty2  in
                                           let uu____80843 =
                                             do_unify e t11 t21  in
                                           tac_and uu____80839 uu____80843)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____80746
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____80891  ->
             let uu____80892 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____80892
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
        (fun uu____80926  ->
           let uu____80927 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____80927)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____80938 =
      mlog
        (fun uu____80943  ->
           let uu____80944 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____80944)
        (fun uu____80949  ->
           let uu____80950 = cur_goal ()  in
           bind uu____80950
             (fun g  ->
                let uu____80956 =
                  let uu____80965 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____80965 ty  in
                bind uu____80956
                  (fun uu____80977  ->
                     match uu____80977 with
                     | (ty1,uu____80987,guard) ->
                         let uu____80989 =
                           let uu____80992 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____80992 guard  in
                         bind uu____80989
                           (fun uu____80996  ->
                              let uu____80997 =
                                let uu____81001 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____81002 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____81001 uu____81002 ty1  in
                              bind uu____80997
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____81011 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____81011
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops]  in
                                      let ng =
                                        let uu____81018 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____81019 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____81018
                                          uu____81019
                                         in
                                      let nty =
                                        let uu____81021 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____81021 ty1  in
                                      let uu____81022 =
                                        let uu____81026 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____81026 ng nty  in
                                      bind uu____81022
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____81035 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____81035
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____80938
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) Prims.list tac)
  =
  fun s_tm  ->
    let uu____81109 =
      let uu____81118 = cur_goal ()  in
      bind uu____81118
        (fun g  ->
           let uu____81130 =
             let uu____81139 = FStar_Tactics_Types.goal_env g  in
             __tc uu____81139 s_tm  in
           bind uu____81130
             (fun uu____81157  ->
                match uu____81157 with
                | (s_tm1,s_ty,guard) ->
                    let uu____81175 =
                      let uu____81178 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____81178 guard  in
                    bind uu____81175
                      (fun uu____81191  ->
                         let uu____81192 =
                           FStar_Syntax_Util.head_and_args' s_ty  in
                         match uu____81192 with
                         | (h,args) ->
                             let uu____81237 =
                               let uu____81244 =
                                 let uu____81245 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____81245.FStar_Syntax_Syntax.n  in
                               match uu____81244 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____81260;
                                      FStar_Syntax_Syntax.vars = uu____81261;_},us)
                                   -> ret (fv, us)
                               | uu____81271 -> fail "type is not an fv"  in
                             bind uu____81237
                               (fun uu____81292  ->
                                  match uu____81292 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____81308 =
                                        let uu____81311 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____81311 t_lid
                                         in
                                      (match uu____81308 with
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
                                                  (fun uu____81362  ->
                                                     let uu____81363 =
                                                       FStar_Syntax_Subst.open_term
                                                         t_ps t_ty
                                                        in
                                                     match uu____81363 with
                                                     | (t_ps1,t_ty1) ->
                                                         let uu____81378 =
                                                           mapM
                                                             (fun c_lid  ->
                                                                let uu____81406
                                                                  =
                                                                  let uu____81409
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                  FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____81409
                                                                    c_lid
                                                                   in
                                                                match uu____81406
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
                                                                    uu____81483
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
                                                                    let uu____81488
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____81488
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____81511
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____81511
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____81554
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs
                                                                     in
                                                                    (match uu____81554
                                                                    with
                                                                    | 
                                                                    (d_ps,bs1)
                                                                    ->
                                                                    let uu____81627
                                                                    =
                                                                    let uu____81629
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp  in
                                                                    Prims.op_Negation
                                                                    uu____81629
                                                                     in
                                                                    failwhen
                                                                    uu____81627
                                                                    "not total?"
                                                                    (fun
                                                                    uu____81648
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
                                                                    uu___614_81665
                                                                    =
                                                                    match uu___614_81665
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____81669)
                                                                    -> true
                                                                    | 
                                                                    uu____81672
                                                                    -> false
                                                                     in
                                                                    let uu____81676
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____81676
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
                                                                    uu____81810
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
                                                                    uu____81872
                                                                     ->
                                                                    match uu____81872
                                                                    with
                                                                    | 
                                                                    ((bv,uu____81892),
                                                                    (t,uu____81894))
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
                                                                    uu____81964
                                                                     ->
                                                                    match uu____81964
                                                                    with
                                                                    | 
                                                                    ((bv,uu____81991),
                                                                    (t,uu____81993))
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
                                                                    uu____82052
                                                                     ->
                                                                    match uu____82052
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
                                                                    let uu____82107
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___2450_82124
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___2450_82124.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___2450_82124.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___2450_82124.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___2450_82124.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___2450_82124.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___2450_82124.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___2450_82124.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___2450_82124.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___2450_82124.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___2450_82124.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___2450_82124.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___2450_82124.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___2450_82124.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___2450_82124.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___2450_82124.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___2450_82124.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___2450_82124.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___2450_82124.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___2450_82124.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___2450_82124.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___2450_82124.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___2450_82124.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___2450_82124.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___2450_82124.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___2450_82124.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___2450_82124.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___2450_82124.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___2450_82124.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___2450_82124.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___2450_82124.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___2450_82124.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___2450_82124.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___2450_82124.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___2450_82124.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___2450_82124.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___2450_82124.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___2450_82124.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___2450_82124.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___2450_82124.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___2450_82124.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___2450_82124.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___2450_82124.FStar_TypeChecker_Env.nbe)
                                                                    }) s_ty
                                                                    pat  in
                                                                    match uu____82107
                                                                    with
                                                                    | 
                                                                    (uu____82138,uu____82139,uu____82140,pat_t,uu____82142,_guard_pat)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____82149
                                                                    =
                                                                    let uu____82150
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____82150
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____82149
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____82155
                                                                    =
                                                                    let uu____82164
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____82164]
                                                                     in
                                                                    let uu____82183
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____82155
                                                                    uu____82183
                                                                     in
                                                                    let nty =
                                                                    let uu____82189
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____82189
                                                                     in
                                                                    let uu____82192
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____82192
                                                                    (fun
                                                                    uu____82222
                                                                     ->
                                                                    match uu____82222
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
                                                                    let uu____82249
                                                                    =
                                                                    let uu____82260
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____82260]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____82249
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____82296
                                                                    =
                                                                    let uu____82307
                                                                    =
                                                                    let uu____82312
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2)  in
                                                                    (fv1,
                                                                    uu____82312)
                                                                     in
                                                                    (g', br,
                                                                    uu____82307)
                                                                     in
                                                                    ret
                                                                    uu____82296))))))
                                                                    | 
                                                                    uu____82333
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                             c_lids
                                                            in
                                                         bind uu____81378
                                                           (fun goal_brs  ->
                                                              let uu____82383
                                                                =
                                                                FStar_List.unzip3
                                                                  goal_brs
                                                                 in
                                                              match uu____82383
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
                                                                  let uu____82456
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                  bind
                                                                    uu____82456
                                                                    (
                                                                    fun
                                                                    uu____82467
                                                                     ->
                                                                    let uu____82468
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____82468
                                                                    (fun
                                                                    uu____82478
                                                                     ->
                                                                    ret infos))))
                                            | uu____82485 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____81109
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____82534::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____82564 = init xs  in x :: uu____82564
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____82577 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      let t3 = FStar_Syntax_Util.unlazy_emb t2  in
      match t3.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____82586) -> inspect t4
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____82652 = last args  in
          (match uu____82652 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____82682 =
                 let uu____82683 =
                   let uu____82688 =
                     let uu____82689 =
                       let uu____82694 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____82694  in
                     uu____82689 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____82688, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____82683  in
               FStar_All.pipe_left ret uu____82682)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____82707,uu____82708) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
          let uu____82761 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____82761 with
           | (bs1,t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____82803 =
                      let uu____82804 =
                        let uu____82809 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____82809)  in
                      FStar_Reflection_Data.Tv_Abs uu____82804  in
                    FStar_All.pipe_left ret uu____82803))
      | FStar_Syntax_Syntax.Tm_type uu____82812 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____82837 ->
          let uu____82852 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____82852 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____82883 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____82883 with
           | (b',t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____82936 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____82949 =
            let uu____82950 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____82950  in
          FStar_All.pipe_left ret uu____82949
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____82971 =
            let uu____82972 =
              let uu____82977 =
                let uu____82978 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____82978  in
              (uu____82977, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____82972  in
          FStar_All.pipe_left ret uu____82971
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____83018 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____83023 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____83023 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____83076 ->
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
             | FStar_Util.Inr uu____83118 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____83122 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____83122 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____83142 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____83148 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____83203 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____83203
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____83224 =
                  let uu____83231 =
                    FStar_List.map
                      (fun uu____83244  ->
                         match uu____83244 with
                         | (p1,uu____83253) -> inspect_pat p1) ps
                     in
                  (fv, uu____83231)  in
                FStar_Reflection_Data.Pat_Cons uu____83224
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
              (fun uu___615_83349  ->
                 match uu___615_83349 with
                 | (pat,uu____83371,t5) ->
                     let uu____83389 = inspect_pat pat  in (uu____83389, t5))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____83398 ->
          ((let uu____83400 =
              let uu____83406 =
                let uu____83408 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____83410 = FStar_Syntax_Print.term_to_string t3  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____83408 uu____83410
                 in
              (FStar_Errors.Warning_CantInspect, uu____83406)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____83400);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____82577
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____83428 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____83428
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____83432 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____83432
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____83436 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____83436
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____83443 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____83443
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____83468 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____83468
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____83485 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____83485
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____83504 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____83504
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____83508 =
          let uu____83509 =
            let uu____83516 =
              let uu____83517 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____83517  in
            FStar_Syntax_Syntax.mk uu____83516  in
          uu____83509 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____83508
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____83525 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____83525
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____83536 =
          let uu____83537 =
            let uu____83544 =
              let uu____83545 =
                let uu____83559 =
                  let uu____83562 =
                    let uu____83563 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____83563]  in
                  FStar_Syntax_Subst.close uu____83562 t2  in
                ((false, [lb]), uu____83559)  in
              FStar_Syntax_Syntax.Tm_let uu____83545  in
            FStar_Syntax_Syntax.mk uu____83544  in
          uu____83537 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____83536
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____83608 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____83608 with
         | (lbs,body) ->
             let uu____83623 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____83623)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____83660 =
                let uu____83661 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____83661  in
              FStar_All.pipe_left wrap uu____83660
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____83668 =
                let uu____83669 =
                  let uu____83683 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____83701 = pack_pat p1  in
                         (uu____83701, false)) ps
                     in
                  (fv, uu____83683)  in
                FStar_Syntax_Syntax.Pat_cons uu____83669  in
              FStar_All.pipe_left wrap uu____83668
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
            (fun uu___616_83750  ->
               match uu___616_83750 with
               | (pat,t1) ->
                   let uu____83767 = pack_pat pat  in
                   (uu____83767, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____83815 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____83815
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____83843 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____83843
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____83889 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____83889
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____83928 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____83928
  
let (lget :
  FStar_Reflection_Data.typ -> Prims.string -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun k  ->
      let uu____83948 =
        bind get
          (fun ps  ->
             let uu____83954 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____83954 with
             | FStar_Pervasives_Native.None  -> fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
      FStar_All.pipe_left (wrap_err "lget") uu____83948
  
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit tac)
  =
  fun _ty  ->
    fun k  ->
      fun t  ->
        let uu____83988 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___2748_83995 = ps  in
                 let uu____83996 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t
                    in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___2748_83995.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___2748_83995.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___2748_83995.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___2748_83995.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___2748_83995.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___2748_83995.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___2748_83995.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___2748_83995.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___2748_83995.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___2748_83995.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___2748_83995.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___2748_83995.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____83996
                 }  in
               set ps1)
           in
        FStar_All.pipe_left (wrap_err "lset") uu____83988
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal * FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun typ  ->
      let uu____84023 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____84023 with
      | (u,ctx_uvars,g_u) ->
          let uu____84056 = FStar_List.hd ctx_uvars  in
          (match uu____84056 with
           | (ctx_uvar,uu____84070) ->
               let g =
                 let uu____84072 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____84072 false
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
        let uu____84095 = goal_of_goal_ty env typ  in
        match uu____84095 with
        | (g,g_u) ->
            let ps =
              let uu____84107 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "TacVerbose")
                 in
              let uu____84110 = FStar_Util.psmap_empty ()  in
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
                FStar_Tactics_Types.tac_verb_dbg = uu____84107;
                FStar_Tactics_Types.local_state = uu____84110
              }  in
            let uu____84120 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____84120)
  