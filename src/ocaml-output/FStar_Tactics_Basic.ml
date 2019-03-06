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
    let uu____64677 =
      let uu____64678 = FStar_Tactics_Types.goal_env g  in
      let uu____64679 = FStar_Tactics_Types.goal_type g  in
      bnorm uu____64678 uu____64679  in
    FStar_Tactics_Types.goal_with_type g uu____64677
  
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
      let uu____64793 = FStar_Options.tactics_failhard ()  in
      if uu____64793
      then run t p
      else
        (try (fun uu___640_64803  -> match () with | () -> run t p) ()
         with
         | FStar_Errors.Err (uu____64812,msg) ->
             FStar_Tactics_Result.Failed
               ((FStar_Tactics_Types.TacticFailure msg), p)
         | FStar_Errors.Error (uu____64816,msg,uu____64818) ->
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
           let uu____64898 = run t1 p  in
           match uu____64898 with
           | FStar_Tactics_Result.Success (a,q) ->
               let uu____64905 = t2 a  in run uu____64905 q
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
    let uu____64928 =
      FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head  in
    match uu____64928 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (check_goal_solved :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun goal  -> get_uvar_solved goal.FStar_Tactics_Types.goal_ctx_uvar 
let (goal_to_string_verbose : FStar_Tactics_Types.goal -> Prims.string) =
  fun g  ->
    let uu____64950 =
      FStar_Syntax_Print.ctx_uvar_to_string
        g.FStar_Tactics_Types.goal_ctx_uvar
       in
    let uu____64952 =
      let uu____64954 = check_goal_solved g  in
      match uu____64954 with
      | FStar_Pervasives_Native.None  -> ""
      | FStar_Pervasives_Native.Some t ->
          let uu____64960 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "\tGOAL ALREADY SOLVED!: %s" uu____64960
       in
    FStar_Util.format2 "%s%s\n" uu____64950 uu____64952
  
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
            let uu____65007 = FStar_Options.print_implicits ()  in
            if uu____65007
            then
              let uu____65011 = FStar_Tactics_Types.goal_env g  in
              let uu____65012 = FStar_Tactics_Types.goal_witness g  in
              tts uu____65011 uu____65012
            else
              (let uu____65015 =
                 get_uvar_solved g.FStar_Tactics_Types.goal_ctx_uvar  in
               match uu____65015 with
               | FStar_Pervasives_Native.None  -> "_"
               | FStar_Pervasives_Native.Some t ->
                   let uu____65021 = FStar_Tactics_Types.goal_env g  in
                   let uu____65022 = FStar_Tactics_Types.goal_witness g  in
                   tts uu____65021 uu____65022)
             in
          let num =
            match maybe_num with
            | FStar_Pervasives_Native.None  -> ""
            | FStar_Pervasives_Native.Some (i,n1) ->
                let uu____65045 = FStar_Util.string_of_int i  in
                let uu____65047 = FStar_Util.string_of_int n1  in
                FStar_Util.format2 " %s/%s" uu____65045 uu____65047
             in
          let maybe_label =
            match g.FStar_Tactics_Types.label with
            | "" -> ""
            | l -> Prims.op_Hat " (" (Prims.op_Hat l ")")  in
          let actual_goal =
            if ps.FStar_Tactics_Types.tac_verb_dbg
            then goal_to_string_verbose g
            else
              (let uu____65065 =
                 FStar_Syntax_Print.binders_to_string ", "
                   (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
                  in
               let uu____65068 =
                 let uu____65070 = FStar_Tactics_Types.goal_env g  in
                 tts uu____65070
                   (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                  in
               FStar_Util.format3 "%s |- %s : %s\n" uu____65065 w uu____65068)
             in
          FStar_Util.format4 "%s%s%s:\n%s\n" kind num maybe_label actual_goal
  
let (tacprint : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      let uu____65097 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____65097
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____65122 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____65122
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____65154 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____65154
  
let (comp_to_typ : FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____65164) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____65174) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (get_phi :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun g  ->
    let uu____65194 =
      let uu____65195 = FStar_Tactics_Types.goal_env g  in
      let uu____65196 = FStar_Tactics_Types.goal_type g  in
      FStar_TypeChecker_Normalize.unfold_whnf uu____65195 uu____65196  in
    FStar_Syntax_Util.un_squash uu____65194
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  -> let uu____65205 = get_phi g  in FStar_Option.isSome uu____65205 
let (print : Prims.string -> unit tac) = fun msg  -> tacprint msg; ret () 
let (debugging : unit -> Prims.bool tac) =
  fun uu____65229  ->
    bind get
      (fun ps  ->
         let uu____65237 =
           FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
             (FStar_Options.Other "Tac")
            in
         ret uu____65237)
  
let (ps_to_string :
  (Prims.string * FStar_Tactics_Types.proofstate) -> Prims.string) =
  fun uu____65252  ->
    match uu____65252 with
    | (msg,ps) ->
        let p_imp imp =
          FStar_Syntax_Print.uvar_to_string
            (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
           in
        let n_active = FStar_List.length ps.FStar_Tactics_Types.goals  in
        let n_smt = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
        let n1 = n_active + n_smt  in
        let uu____65274 =
          let uu____65278 =
            let uu____65282 =
              let uu____65284 =
                FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
              FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____65284
                msg
               in
            let uu____65287 =
              let uu____65291 =
                if
                  ps.FStar_Tactics_Types.entry_range <>
                    FStar_Range.dummyRange
                then
                  let uu____65295 =
                    FStar_Range.string_of_def_range
                      ps.FStar_Tactics_Types.entry_range
                     in
                  FStar_Util.format1 "Location: %s\n" uu____65295
                else ""  in
              let uu____65301 =
                let uu____65305 =
                  let uu____65307 =
                    FStar_TypeChecker_Env.debug
                      ps.FStar_Tactics_Types.main_context
                      (FStar_Options.Other "Imp")
                     in
                  if uu____65307
                  then
                    let uu____65312 =
                      FStar_Common.string_of_list p_imp
                        ps.FStar_Tactics_Types.all_implicits
                       in
                    FStar_Util.format1 "Imps: %s\n" uu____65312
                  else ""  in
                [uu____65305]  in
              uu____65291 :: uu____65301  in
            uu____65282 :: uu____65287  in
          let uu____65322 =
            let uu____65326 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "Goal"
                       (FStar_Pervasives_Native.Some
                          (((Prims.parse_int "1") + i), n1)) ps g)
                ps.FStar_Tactics_Types.goals
               in
            let uu____65346 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "SMT Goal"
                       (FStar_Pervasives_Native.Some
                          ((((Prims.parse_int "1") + n_active) + i), n1)) ps
                       g) ps.FStar_Tactics_Types.smt_goals
               in
            FStar_List.append uu____65326 uu____65346  in
          FStar_List.append uu____65278 uu____65322  in
        FStar_String.concat "" uu____65274
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      let uu____65376 =
        let uu____65377 = FStar_Tactics_Types.goal_env g  in
        FStar_TypeChecker_Env.all_binders uu____65377  in
      let uu____65378 =
        let uu____65383 =
          let uu____65384 = FStar_Tactics_Types.goal_env g  in
          FStar_TypeChecker_Env.dsenv uu____65384  in
        FStar_Syntax_Print.binders_to_json uu____65383  in
      FStar_All.pipe_right uu____65376 uu____65378  in
    let uu____65385 =
      let uu____65393 =
        let uu____65401 =
          let uu____65407 =
            let uu____65408 =
              let uu____65416 =
                let uu____65422 =
                  let uu____65423 =
                    let uu____65425 = FStar_Tactics_Types.goal_env g  in
                    let uu____65426 = FStar_Tactics_Types.goal_witness g  in
                    tts uu____65425 uu____65426  in
                  FStar_Util.JsonStr uu____65423  in
                ("witness", uu____65422)  in
              let uu____65429 =
                let uu____65437 =
                  let uu____65443 =
                    let uu____65444 =
                      let uu____65446 = FStar_Tactics_Types.goal_env g  in
                      let uu____65447 = FStar_Tactics_Types.goal_type g  in
                      tts uu____65446 uu____65447  in
                    FStar_Util.JsonStr uu____65444  in
                  ("type", uu____65443)  in
                [uu____65437;
                ("label", (FStar_Util.JsonStr (g.FStar_Tactics_Types.label)))]
                 in
              uu____65416 :: uu____65429  in
            FStar_Util.JsonAssoc uu____65408  in
          ("goal", uu____65407)  in
        [uu____65401]  in
      ("hyps", g_binders) :: uu____65393  in
    FStar_Util.JsonAssoc uu____65385
  
let (ps_to_json :
  (Prims.string * FStar_Tactics_Types.proofstate) -> FStar_Util.json) =
  fun uu____65501  ->
    match uu____65501 with
    | (msg,ps) ->
        let uu____65511 =
          let uu____65519 =
            let uu____65527 =
              let uu____65535 =
                let uu____65543 =
                  let uu____65549 =
                    let uu____65550 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____65550  in
                  ("goals", uu____65549)  in
                let uu____65555 =
                  let uu____65563 =
                    let uu____65569 =
                      let uu____65570 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____65570  in
                    ("smt-goals", uu____65569)  in
                  [uu____65563]  in
                uu____65543 :: uu____65555  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____65535
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____65527  in
          let uu____65604 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____65620 =
                let uu____65626 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____65626)  in
              [uu____65620]
            else []  in
          FStar_List.append uu____65519 uu____65604  in
        FStar_Util.JsonAssoc uu____65511
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____65666  ->
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
         (let uu____65697 = FStar_Tactics_Types.subst_proof_state subst1 ps
             in
          dump_proofstate uu____65697 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let traise : 'a . Prims.exn -> 'a tac =
  fun e  -> mk_tac (fun ps  -> FStar_Tactics_Result.Failed (e, ps)) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____65770 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____65770
          then dump_proofstate ps (Prims.op_Hat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed
           ((FStar_Tactics_Types.TacticFailure msg), ps))
  
let fail1 : 'Auu____65784 . Prims.string -> Prims.string -> 'Auu____65784 tac
  =
  fun msg  ->
    fun x  -> let uu____65801 = FStar_Util.format1 msg x  in fail uu____65801
  
let fail2 :
  'Auu____65812 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____65812 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        let uu____65836 = FStar_Util.format2 msg x y  in fail uu____65836
  
let fail3 :
  'Auu____65849 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____65849 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____65880 = FStar_Util.format3 msg x y z  in fail uu____65880
  
let fail4 :
  'Auu____65895 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____65895 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____65933 = FStar_Util.format4 msg x y z w  in
            fail uu____65933
  
let catch : 'a . 'a tac -> (Prims.exn,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____65968 = run t ps  in
         match uu____65968 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___802_65992 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___802_65992.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___802_65992.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___802_65992.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___802_65992.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___802_65992.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___802_65992.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___802_65992.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___802_65992.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___802_65992.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___802_65992.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___802_65992.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (uu___802_65992.FStar_Tactics_Types.local_state)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let recover : 'a . 'a tac -> (Prims.exn,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let uu____66031 = run t ps  in
         match uu____66031 with
         | FStar_Tactics_Result.Success (a,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inr a), q)
         | FStar_Tactics_Result.Failed (m,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inl m), q))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____66079 = catch t  in
    bind uu____66079
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____66106 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try
           (fun uu___828_66138  ->
              match () with
              | () -> let uu____66143 = trytac t  in run uu____66143 ps) ()
         with
         | FStar_Errors.Err (uu____66159,msg) ->
             (log ps
                (fun uu____66165  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____66171,msg,uu____66173) ->
             (log ps
                (fun uu____66178  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____66215 = run t ps  in
           match uu____66215 with
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
  fun p  -> mk_tac (fun uu____66239  -> FStar_Tactics_Result.Success ((), p)) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___863_66254 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___863_66254.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___863_66254.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___863_66254.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___863_66254.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___863_66254.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___863_66254.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___863_66254.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___863_66254.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___863_66254.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___863_66254.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___863_66254.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___863_66254.FStar_Tactics_Types.local_state)
            }))
  
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____66278 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____66278
         then
           let uu____66282 = FStar_Syntax_Print.term_to_string t1  in
           let uu____66284 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____66282
             uu____66284
         else ());
        (try
           (fun uu___871_66295  ->
              match () with
              | () ->
                  let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
                  ((let uu____66303 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____66303
                    then
                      let uu____66307 =
                        FStar_Common.string_of_option
                          (FStar_TypeChecker_Rel.guard_to_string env) res
                         in
                      let uu____66309 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____66311 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.print3
                        "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____66307
                        uu____66309 uu____66311
                    else ());
                   (match res with
                    | FStar_Pervasives_Native.None  -> ret false
                    | FStar_Pervasives_Native.Some g ->
                        let uu____66322 =
                          add_implicits g.FStar_TypeChecker_Env.implicits  in
                        bind uu____66322 (fun uu____66327  -> ret true)))) ()
         with
         | FStar_Errors.Err (uu____66337,msg) ->
             mlog
               (fun uu____66343  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____66346  -> ret false)
         | FStar_Errors.Error (uu____66349,msg,r) ->
             mlog
               (fun uu____66357  ->
                  let uu____66358 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____66358) (fun uu____66362  -> ret false))
  
let (compress_implicits : unit tac) =
  bind get
    (fun ps  ->
       let imps = ps.FStar_Tactics_Types.all_implicits  in
       let g =
         let uu___897_66376 = FStar_TypeChecker_Env.trivial_guard  in
         {
           FStar_TypeChecker_Env.guard_f =
             (uu___897_66376.FStar_TypeChecker_Env.guard_f);
           FStar_TypeChecker_Env.deferred =
             (uu___897_66376.FStar_TypeChecker_Env.deferred);
           FStar_TypeChecker_Env.univ_ineqs =
             (uu___897_66376.FStar_TypeChecker_Env.univ_ineqs);
           FStar_TypeChecker_Env.implicits = imps
         }  in
       let g1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g
          in
       let ps' =
         let uu___901_66379 = ps  in
         {
           FStar_Tactics_Types.main_context =
             (uu___901_66379.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___901_66379.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (g1.FStar_TypeChecker_Env.implicits);
           FStar_Tactics_Types.goals =
             (uu___901_66379.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___901_66379.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___901_66379.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___901_66379.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___901_66379.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___901_66379.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___901_66379.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___901_66379.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___901_66379.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___901_66379.FStar_Tactics_Types.local_state)
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
          (fun uu____66406  ->
             (let uu____66408 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____66408
              then
                (FStar_Options.push ();
                 (let uu____66413 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____66417 = __do_unify env t1 t2  in
              bind uu____66417
                (fun r  ->
                   (let uu____66428 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____66428 then FStar_Options.pop () else ());
                   ret r)))
  
let (remove_solved_goals : unit tac) =
  bind get
    (fun ps  ->
       let ps' =
         let uu___916_66442 = ps  in
         let uu____66443 =
           FStar_List.filter
             (fun g  ->
                let uu____66449 = check_goal_solved g  in
                FStar_Option.isNone uu____66449) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___916_66442.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___916_66442.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___916_66442.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____66443;
           FStar_Tactics_Types.smt_goals =
             (uu___916_66442.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___916_66442.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___916_66442.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___916_66442.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___916_66442.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___916_66442.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___916_66442.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___916_66442.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___916_66442.FStar_Tactics_Types.local_state)
         }  in
       set ps')
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____66467 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____66467 with
      | FStar_Pervasives_Native.Some uu____66472 ->
          let uu____66473 =
            let uu____66475 = goal_to_string_verbose goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____66475  in
          fail uu____66473
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____66496 = FStar_Tactics_Types.goal_env goal  in
      let uu____66497 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____66496 solution uu____66497
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____66504 =
         let uu___929_66505 = p  in
         let uu____66506 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___929_66505.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___929_66505.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___929_66505.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____66506;
           FStar_Tactics_Types.smt_goals =
             (uu___929_66505.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___929_66505.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___929_66505.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___929_66505.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___929_66505.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___929_66505.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___929_66505.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___929_66505.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___929_66505.FStar_Tactics_Types.local_state)
         }  in
       set uu____66504)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      mlog
        (fun uu____66528  ->
           let uu____66529 =
             let uu____66531 = FStar_Tactics_Types.goal_witness goal  in
             FStar_Syntax_Print.term_to_string uu____66531  in
           let uu____66532 = FStar_Syntax_Print.term_to_string solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____66529 uu____66532)
        (fun uu____66537  ->
           let uu____66538 = trysolve goal solution  in
           bind uu____66538
             (fun b  ->
                if b
                then bind __dismiss (fun uu____66550  -> remove_solved_goals)
                else
                  (let uu____66553 =
                     let uu____66555 =
                       let uu____66557 = FStar_Tactics_Types.goal_env goal
                          in
                       tts uu____66557 solution  in
                     let uu____66558 =
                       let uu____66560 = FStar_Tactics_Types.goal_env goal
                          in
                       let uu____66561 =
                         FStar_Tactics_Types.goal_witness goal  in
                       tts uu____66560 uu____66561  in
                     let uu____66562 =
                       let uu____66564 = FStar_Tactics_Types.goal_env goal
                          in
                       let uu____66565 = FStar_Tactics_Types.goal_type goal
                          in
                       tts uu____66564 uu____66565  in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____66555 uu____66558 uu____66562
                      in
                   fail uu____66553)))
  
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____66582 = set_solution goal solution  in
      bind uu____66582
        (fun uu____66586  ->
           bind __dismiss (fun uu____66588  -> remove_solved_goals))
  
let (set_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___945_66607 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___945_66607.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___945_66607.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___945_66607.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals = gs;
              FStar_Tactics_Types.smt_goals =
                (uu___945_66607.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___945_66607.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___945_66607.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___945_66607.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___945_66607.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___945_66607.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___945_66607.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___945_66607.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___945_66607.FStar_Tactics_Types.local_state)
            }))
  
let (set_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___949_66626 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___949_66626.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___949_66626.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___949_66626.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___949_66626.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals = gs;
              FStar_Tactics_Types.depth =
                (uu___949_66626.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___949_66626.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___949_66626.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___949_66626.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___949_66626.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___949_66626.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___949_66626.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___949_66626.FStar_Tactics_Types.local_state)
            }))
  
let (dismiss_all : unit tac) = set_goals [] 
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____66642 = FStar_Options.defensive ()  in
    if uu____66642
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____66652 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____66652)
         in
      let b2 =
        b1 &&
          (let uu____66656 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____66656)
         in
      let rec aux b3 e =
        let uu____66671 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____66671 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____66691 =
        (let uu____66695 = aux b2 env  in Prims.op_Negation uu____66695) &&
          (let uu____66698 = FStar_ST.op_Bang nwarn  in
           uu____66698 < (Prims.parse_int "5"))
         in
      (if uu____66691
       then
         ((let uu____66724 =
             let uu____66725 = FStar_Tactics_Types.goal_type g  in
             uu____66725.FStar_Syntax_Syntax.pos  in
           let uu____66728 =
             let uu____66734 =
               let uu____66736 = goal_to_string_verbose g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____66736
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____66734)  in
           FStar_Errors.log_issue uu____66724 uu____66728);
          (let uu____66740 =
             let uu____66742 = FStar_ST.op_Bang nwarn  in
             uu____66742 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____66740))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___971_66811 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___971_66811.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___971_66811.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___971_66811.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___971_66811.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___971_66811.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___971_66811.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___971_66811.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___971_66811.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___971_66811.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___971_66811.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___971_66811.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___971_66811.FStar_Tactics_Types.local_state)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___976_66832 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___976_66832.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___976_66832.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___976_66832.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___976_66832.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___976_66832.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___976_66832.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___976_66832.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___976_66832.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___976_66832.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___976_66832.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___976_66832.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___976_66832.FStar_Tactics_Types.local_state)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___981_66853 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___981_66853.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___981_66853.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___981_66853.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___981_66853.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___981_66853.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___981_66853.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___981_66853.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___981_66853.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___981_66853.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___981_66853.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___981_66853.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___981_66853.FStar_Tactics_Types.local_state)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___986_66874 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___986_66874.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___986_66874.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___986_66874.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___986_66874.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___986_66874.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___986_66874.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___986_66874.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___986_66874.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___986_66874.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___986_66874.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___986_66874.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___986_66874.FStar_Tactics_Types.local_state)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____66886  -> add_goals [g]) 
let (new_uvar :
  Prims.string ->
    env ->
      FStar_Reflection_Data.typ ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar) tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____66917 =
          FStar_TypeChecker_Env.new_implicit_var_aux reason
            typ.FStar_Syntax_Syntax.pos env typ
            FStar_Syntax_Syntax.Allow_untyped FStar_Pervasives_Native.None
           in
        match uu____66917 with
        | (u,ctx_uvar,g_u) ->
            let uu____66955 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____66955
              (fun uu____66964  ->
                 let uu____66965 =
                   let uu____66970 =
                     let uu____66971 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____66971  in
                   (u, uu____66970)  in
                 ret uu____66965)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____66992 = FStar_Syntax_Util.un_squash t1  in
    match uu____66992 with
    | FStar_Pervasives_Native.Some t' ->
        let t'1 = FStar_Syntax_Util.unascribe t'  in
        let uu____67004 =
          let uu____67005 = FStar_Syntax_Subst.compress t'1  in
          uu____67005.FStar_Syntax_Syntax.n  in
        (match uu____67004 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____67010 -> false)
    | uu____67012 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____67025 = FStar_Syntax_Util.un_squash t  in
    match uu____67025 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____67036 =
          let uu____67037 = FStar_Syntax_Subst.compress t'  in
          uu____67037.FStar_Syntax_Syntax.n  in
        (match uu____67036 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____67042 -> false)
    | uu____67044 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____67057  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____67069 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____67069 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____67076 = goal_to_string_verbose hd1  in
                    let uu____67078 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____67076 uu____67078);
                   ret hd1)))
  
let (tadmit_t : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____67091 =
      bind get
        (fun ps  ->
           let uu____67097 = cur_goal ()  in
           bind uu____67097
             (fun g  ->
                (let uu____67104 =
                   let uu____67105 = FStar_Tactics_Types.goal_type g  in
                   uu____67105.FStar_Syntax_Syntax.pos  in
                 let uu____67108 =
                   let uu____67114 =
                     let uu____67116 =
                       goal_to_string "" FStar_Pervasives_Native.None ps g
                        in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____67116
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____67114)  in
                 FStar_Errors.log_issue uu____67104 uu____67108);
                solve' g t))
       in
    FStar_All.pipe_left (wrap_err "tadmit_t") uu____67091
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____67139  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___1031_67150 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___1031_67150.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___1031_67150.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___1031_67150.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___1031_67150.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___1031_67150.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___1031_67150.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___1031_67150.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___1031_67150.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___1031_67150.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___1031_67150.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___1031_67150.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (uu___1031_67150.FStar_Tactics_Types.local_state)
           }  in
         let uu____67152 = set ps1  in
         bind uu____67152
           (fun uu____67157  ->
              let uu____67158 = FStar_BigInt.of_int_fs n1  in ret uu____67158))
  
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
              let uu____67196 = env.FStar_TypeChecker_Env.universe_of env phi
                 in
              FStar_Syntax_Util.mk_squash uu____67196 phi  in
            let uu____67197 = new_uvar reason env typ  in
            bind uu____67197
              (fun uu____67212  ->
                 match uu____67212 with
                 | (uu____67219,ctx_uvar) ->
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
             (fun uu____67266  ->
                let uu____67267 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____67267)
             (fun uu____67272  ->
                let e1 =
                  let uu___1049_67274 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1049_67274.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1049_67274.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1049_67274.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1049_67274.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1049_67274.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1049_67274.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1049_67274.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1049_67274.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1049_67274.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1049_67274.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1049_67274.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1049_67274.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1049_67274.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1049_67274.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1049_67274.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1049_67274.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1049_67274.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1049_67274.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1049_67274.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1049_67274.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1049_67274.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1049_67274.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1049_67274.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1049_67274.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1049_67274.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1049_67274.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1049_67274.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1049_67274.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1049_67274.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1049_67274.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1049_67274.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1049_67274.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1049_67274.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1049_67274.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1049_67274.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1049_67274.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1049_67274.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1049_67274.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1049_67274.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1049_67274.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1049_67274.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1049_67274.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___1053_67286  ->
                     match () with
                     | () ->
                         let uu____67295 =
                           FStar_TypeChecker_TcTerm.type_of_tot_term e1 t  in
                         ret uu____67295) ()
                with
                | FStar_Errors.Err (uu____67322,msg) ->
                    let uu____67326 = tts e1 t  in
                    let uu____67328 =
                      let uu____67330 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____67330
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____67326 uu____67328 msg
                | FStar_Errors.Error (uu____67340,msg,uu____67342) ->
                    let uu____67345 = tts e1 t  in
                    let uu____67347 =
                      let uu____67349 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____67349
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____67345 uu____67347 msg))
  
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
             (fun uu____67402  ->
                let uu____67403 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc_ghost(%s)\n" uu____67403)
             (fun uu____67408  ->
                let e1 =
                  let uu___1070_67410 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1070_67410.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1070_67410.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1070_67410.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1070_67410.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1070_67410.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1070_67410.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1070_67410.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1070_67410.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1070_67410.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1070_67410.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1070_67410.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1070_67410.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1070_67410.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1070_67410.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1070_67410.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1070_67410.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1070_67410.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1070_67410.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1070_67410.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1070_67410.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1070_67410.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1070_67410.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1070_67410.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1070_67410.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1070_67410.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1070_67410.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1070_67410.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1070_67410.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1070_67410.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1070_67410.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1070_67410.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1070_67410.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1070_67410.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1070_67410.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1070_67410.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1070_67410.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1070_67410.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1070_67410.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1070_67410.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1070_67410.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1070_67410.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1070_67410.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___1074_67425  ->
                     match () with
                     | () ->
                         let uu____67434 =
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e1 t
                            in
                         (match uu____67434 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____67472,msg) ->
                    let uu____67476 = tts e1 t  in
                    let uu____67478 =
                      let uu____67480 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____67480
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____67476 uu____67478 msg
                | FStar_Errors.Error (uu____67490,msg,uu____67492) ->
                    let uu____67495 = tts e1 t  in
                    let uu____67497 =
                      let uu____67499 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____67499
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____67495 uu____67497 msg))
  
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
             (fun uu____67552  ->
                let uu____67553 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____67553)
             (fun uu____67559  ->
                let e1 =
                  let uu___1095_67561 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1095_67561.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1095_67561.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1095_67561.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1095_67561.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1095_67561.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1095_67561.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1095_67561.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1095_67561.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1095_67561.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1095_67561.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1095_67561.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1095_67561.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1095_67561.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1095_67561.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1095_67561.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1095_67561.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1095_67561.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1095_67561.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1095_67561.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1095_67561.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1095_67561.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1095_67561.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1095_67561.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1095_67561.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1095_67561.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1095_67561.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1095_67561.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1095_67561.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1095_67561.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1095_67561.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1095_67561.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1095_67561.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1095_67561.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1095_67561.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1095_67561.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1095_67561.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1095_67561.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1095_67561.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1095_67561.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1095_67561.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1095_67561.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1095_67561.FStar_TypeChecker_Env.nbe)
                  }  in
                let e2 =
                  let uu___1098_67564 = e1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1098_67564.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1098_67564.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1098_67564.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1098_67564.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1098_67564.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1098_67564.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1098_67564.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1098_67564.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1098_67564.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1098_67564.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1098_67564.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1098_67564.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1098_67564.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1098_67564.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1098_67564.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1098_67564.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1098_67564.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1098_67564.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1098_67564.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1098_67564.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1098_67564.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1098_67564.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1098_67564.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1098_67564.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___1098_67564.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1098_67564.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1098_67564.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1098_67564.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1098_67564.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1098_67564.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1098_67564.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1098_67564.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1098_67564.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1098_67564.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1098_67564.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1098_67564.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1098_67564.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1098_67564.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1098_67564.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1098_67564.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1098_67564.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1098_67564.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___1102_67579  ->
                     match () with
                     | () ->
                         let uu____67588 =
                           FStar_TypeChecker_TcTerm.tc_term e2 t  in
                         (match uu____67588 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____67626,msg) ->
                    let uu____67630 = tts e2 t  in
                    let uu____67632 =
                      let uu____67634 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____67634
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____67630 uu____67632 msg
                | FStar_Errors.Error (uu____67644,msg,uu____67646) ->
                    let uu____67649 = tts e2 t  in
                    let uu____67651 =
                      let uu____67653 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____67653
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____67649 uu____67651 msg))
  
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
  fun uu____67687  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___1127_67706 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___1127_67706.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___1127_67706.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___1127_67706.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___1127_67706.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___1127_67706.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___1127_67706.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___1127_67706.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___1127_67706.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___1127_67706.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___1127_67706.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___1127_67706.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___1127_67706.FStar_Tactics_Types.local_state)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____67731 = get_guard_policy ()  in
      bind uu____67731
        (fun old_pol  ->
           let uu____67737 = set_guard_policy pol  in
           bind uu____67737
             (fun uu____67741  ->
                bind t
                  (fun r  ->
                     let uu____67745 = set_guard_policy old_pol  in
                     bind uu____67745 (fun uu____67749  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____67753 = let uu____67758 = cur_goal ()  in trytac uu____67758  in
  bind uu____67753
    (fun uu___609_67765  ->
       match uu___609_67765 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____67771 = FStar_Options.peek ()  in ret uu____67771)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        mlog
          (fun uu____67796  ->
             let uu____67797 = FStar_TypeChecker_Rel.guard_to_string e g  in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason
               uu____67797)
          (fun uu____67802  ->
             let uu____67803 =
               add_implicits g.FStar_TypeChecker_Env.implicits  in
             bind uu____67803
               (fun uu____67807  ->
                  bind getopts
                    (fun opts  ->
                       let uu____67811 =
                         let uu____67812 =
                           FStar_TypeChecker_Rel.simplify_guard e g  in
                         uu____67812.FStar_TypeChecker_Env.guard_f  in
                       match uu____67811 with
                       | FStar_TypeChecker_Common.Trivial  -> ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____67816 = istrivial e f  in
                           if uu____67816
                           then ret ()
                           else
                             bind get
                               (fun ps  ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop  ->
                                      ((let uu____67829 =
                                          let uu____67835 =
                                            let uu____67837 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g
                                               in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____67837
                                             in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____67835)
                                           in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____67829);
                                       ret ())
                                  | FStar_Tactics_Types.Goal  ->
                                      mlog
                                        (fun uu____67843  ->
                                           let uu____67844 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____67844)
                                        (fun uu____67849  ->
                                           let uu____67850 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____67850
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___1156_67858 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___1156_67858.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___1156_67858.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___1156_67858.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___1156_67858.FStar_Tactics_Types.label)
                                                  }  in
                                                push_goals [goal1]))
                                  | FStar_Tactics_Types.SMT  ->
                                      mlog
                                        (fun uu____67862  ->
                                           let uu____67863 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____67863)
                                        (fun uu____67868  ->
                                           let uu____67869 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____67869
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___1163_67877 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___1163_67877.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___1163_67877.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___1163_67877.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___1163_67877.FStar_Tactics_Types.label)
                                                  }  in
                                                push_smt_goals [goal1]))
                                  | FStar_Tactics_Types.Force  ->
                                      mlog
                                        (fun uu____67881  ->
                                           let uu____67882 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____67882)
                                        (fun uu____67886  ->
                                           try
                                             (fun uu___1170_67891  ->
                                                match () with
                                                | () ->
                                                    let uu____67894 =
                                                      let uu____67896 =
                                                        let uu____67898 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____67898
                                                         in
                                                      Prims.op_Negation
                                                        uu____67896
                                                       in
                                                    if uu____67894
                                                    then
                                                      mlog
                                                        (fun uu____67905  ->
                                                           let uu____67906 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g
                                                              in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____67906)
                                                        (fun uu____67910  ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else ret ()) ()
                                           with
                                           | uu___1169_67915 ->
                                               mlog
                                                 (fun uu____67920  ->
                                                    let uu____67921 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g
                                                       in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____67921)
                                                 (fun uu____67925  ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____67937 =
      let uu____67940 = cur_goal ()  in
      bind uu____67940
        (fun goal  ->
           let uu____67946 =
             let uu____67955 = FStar_Tactics_Types.goal_env goal  in
             __tc_lax uu____67955 t  in
           bind uu____67946
             (fun uu____67966  ->
                match uu____67966 with
                | (uu____67975,typ,uu____67977) -> ret typ))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____67937
  
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
            let uu____68017 = mk_irrelevant_goal reason env phi opts label1
               in
            bind uu____68017 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____68029  ->
    let uu____68032 = cur_goal ()  in
    bind uu____68032
      (fun goal  ->
         let uu____68038 =
           let uu____68040 = FStar_Tactics_Types.goal_env goal  in
           let uu____68041 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____68040 uu____68041  in
         if uu____68038
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____68047 =
              let uu____68049 = FStar_Tactics_Types.goal_env goal  in
              let uu____68050 = FStar_Tactics_Types.goal_type goal  in
              tts uu____68049 uu____68050  in
            fail1 "Not a trivial goal: %s" uu____68047))
  
let divide : 'a 'b . FStar_BigInt.t -> 'a tac -> 'b tac -> ('a * 'b) tac =
  fun n1  ->
    fun l  ->
      fun r  ->
        bind get
          (fun p  ->
             let uu____68101 =
               try
                 (fun uu___1226_68124  ->
                    match () with
                    | () ->
                        let uu____68135 =
                          let uu____68144 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____68144
                            p.FStar_Tactics_Types.goals
                           in
                        ret uu____68135) ()
               with | uu___1225_68155 -> fail "divide: not enough goals"  in
             bind uu____68101
               (fun uu____68192  ->
                  match uu____68192 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___1208_68218 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___1208_68218.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___1208_68218.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___1208_68218.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___1208_68218.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___1208_68218.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___1208_68218.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___1208_68218.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___1208_68218.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___1208_68218.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___1208_68218.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___1208_68218.FStar_Tactics_Types.local_state)
                        }  in
                      let uu____68219 = set lp  in
                      bind uu____68219
                        (fun uu____68227  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___1214_68243 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___1214_68243.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___1214_68243.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___1214_68243.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___1214_68243.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___1214_68243.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___1214_68243.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___1214_68243.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___1214_68243.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___1214_68243.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___1214_68243.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___1214_68243.FStar_Tactics_Types.local_state)
                                       }  in
                                     let uu____68244 = set rp  in
                                     bind uu____68244
                                       (fun uu____68252  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___1220_68268 =
                                                        rp'  in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___1220_68268.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___1220_68268.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___1220_68268.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___1220_68268.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___1220_68268.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___1220_68268.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___1220_68268.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___1220_68268.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___1220_68268.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___1220_68268.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___1220_68268.FStar_Tactics_Types.local_state)
                                                      }  in
                                                    let uu____68269 = set p'
                                                       in
                                                    bind uu____68269
                                                      (fun uu____68277  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____68283 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____68305 = divide FStar_BigInt.one f idtac  in
    bind uu____68305
      (fun uu____68318  -> match uu____68318 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____68356::uu____68357 ->
             let uu____68360 =
               let uu____68369 = map tau  in
               divide FStar_BigInt.one tau uu____68369  in
             bind uu____68360
               (fun uu____68387  ->
                  match uu____68387 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____68429 =
        bind t1
          (fun uu____68434  ->
             let uu____68435 = map t2  in
             bind uu____68435 (fun uu____68443  -> ret ()))
         in
      focus uu____68429
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____68453  ->
    let uu____68456 =
      let uu____68459 = cur_goal ()  in
      bind uu____68459
        (fun goal  ->
           let uu____68468 =
             let uu____68475 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____68475  in
           match uu____68468 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____68484 =
                 let uu____68486 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____68486  in
               if uu____68484
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____68495 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____68495 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____68509 = new_uvar "intro" env' typ'  in
                  bind uu____68509
                    (fun uu____68526  ->
                       match uu____68526 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c))
                              in
                           let uu____68550 = set_solution goal sol  in
                           bind uu____68550
                             (fun uu____68556  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                    goal.FStar_Tactics_Types.label
                                   in
                                let uu____68558 =
                                  let uu____68561 = bnorm_goal g  in
                                  replace_cur uu____68561  in
                                bind uu____68558 (fun uu____68563  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____68568 =
                 let uu____68570 = FStar_Tactics_Types.goal_env goal  in
                 let uu____68571 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____68570 uu____68571  in
               fail1 "goal is not an arrow (%s)" uu____68568)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____68456
  
let (intro_rec :
  unit -> (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder) tac) =
  fun uu____68589  ->
    let uu____68596 = cur_goal ()  in
    bind uu____68596
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____68615 =
            let uu____68622 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____68622  in
          match uu____68615 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____68635 =
                let uu____68637 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____68637  in
              if uu____68635
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____68654 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____68654
                    in
                 let bs =
                   let uu____68665 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____68665; b]  in
                 let env' =
                   let uu____68691 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____68691 bs  in
                 let uu____68692 =
                   let uu____68699 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____68699  in
                 bind uu____68692
                   (fun uu____68719  ->
                      match uu____68719 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____68733 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____68736 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____68733
                              FStar_Parser_Const.effect_Tot_lid uu____68736
                              [] FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____68754 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____68754 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____68776 =
                                   let uu____68777 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____68777.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____68776
                                  in
                               let uu____68793 = set_solution goal tm  in
                               bind uu____68793
                                 (fun uu____68802  ->
                                    let uu____68803 =
                                      let uu____68806 =
                                        bnorm_goal
                                          (let uu___1291_68809 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___1291_68809.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___1291_68809.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___1291_68809.FStar_Tactics_Types.is_guard);
                                             FStar_Tactics_Types.label =
                                               (uu___1291_68809.FStar_Tactics_Types.label)
                                           })
                                         in
                                      replace_cur uu____68806  in
                                    bind uu____68803
                                      (fun uu____68816  ->
                                         let uu____68817 =
                                           let uu____68822 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____68822, b)  in
                                         ret uu____68817)))))
          | FStar_Pervasives_Native.None  ->
              let uu____68831 =
                let uu____68833 = FStar_Tactics_Types.goal_env goal  in
                let uu____68834 = FStar_Tactics_Types.goal_type goal  in
                tts uu____68833 uu____68834  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____68831))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____68854 = cur_goal ()  in
    bind uu____68854
      (fun goal  ->
         mlog
           (fun uu____68861  ->
              let uu____68862 =
                let uu____68864 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____68864  in
              FStar_Util.print1 "norm: witness = %s\n" uu____68862)
           (fun uu____68870  ->
              let steps =
                let uu____68874 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____68874
                 in
              let t =
                let uu____68878 = FStar_Tactics_Types.goal_env goal  in
                let uu____68879 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____68878 uu____68879  in
              let uu____68880 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____68880))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____68905 =
          bind get
            (fun ps  ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
                 | g::uu____68913 -> g.FStar_Tactics_Types.opts
                 | uu____68916 -> FStar_Options.peek ()  in
               mlog
                 (fun uu____68921  ->
                    let uu____68922 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____68922)
                 (fun uu____68927  ->
                    let uu____68928 = __tc_lax e t  in
                    bind uu____68928
                      (fun uu____68949  ->
                         match uu____68949 with
                         | (t1,uu____68959,uu____68960) ->
                             let steps =
                               let uu____68964 =
                                 FStar_TypeChecker_Normalize.tr_norm_steps s
                                  in
                               FStar_List.append
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu____68964
                                in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1
                                in
                             mlog
                               (fun uu____68970  ->
                                  let uu____68971 =
                                    FStar_Syntax_Print.term_to_string t2  in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____68971)
                               (fun uu____68975  -> ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____68905
  
let (refine_intro : unit -> unit tac) =
  fun uu____68988  ->
    let uu____68991 =
      let uu____68994 = cur_goal ()  in
      bind uu____68994
        (fun g  ->
           let uu____69001 =
             let uu____69012 = FStar_Tactics_Types.goal_env g  in
             let uu____69013 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____69012
               uu____69013
              in
           match uu____69001 with
           | (uu____69016,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____69042 =
                 let uu____69047 =
                   let uu____69052 =
                     let uu____69053 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____69053]  in
                   FStar_Syntax_Subst.open_term uu____69052 phi  in
                 match uu____69047 with
                 | (bvs,phi1) ->
                     let uu____69078 =
                       let uu____69079 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____69079  in
                     (uu____69078, phi1)
                  in
               (match uu____69042 with
                | (bv1,phi1) ->
                    let uu____69098 =
                      let uu____69101 = FStar_Tactics_Types.goal_env g  in
                      let uu____69102 =
                        let uu____69103 =
                          let uu____69106 =
                            let uu____69107 =
                              let uu____69114 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____69114)  in
                            FStar_Syntax_Syntax.NT uu____69107  in
                          [uu____69106]  in
                        FStar_Syntax_Subst.subst uu____69103 phi1  in
                      mk_irrelevant_goal "refine_intro refinement"
                        uu____69101 uu____69102 g.FStar_Tactics_Types.opts
                        g.FStar_Tactics_Types.label
                       in
                    bind uu____69098
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____69123  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____68991
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____69146 = cur_goal ()  in
      bind uu____69146
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____69155 = FStar_Tactics_Types.goal_env goal  in
               let uu____69156 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____69155 uu____69156
             else FStar_Tactics_Types.goal_env goal  in
           let uu____69159 = __tc env t  in
           bind uu____69159
             (fun uu____69178  ->
                match uu____69178 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____69193  ->
                         let uu____69194 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____69196 =
                           let uu____69198 =
                             FStar_Tactics_Types.goal_env goal  in
                           FStar_TypeChecker_Rel.guard_to_string uu____69198
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____69194 uu____69196)
                      (fun uu____69202  ->
                         let uu____69203 =
                           let uu____69206 =
                             FStar_Tactics_Types.goal_env goal  in
                           proc_guard "__exact typing" uu____69206 guard  in
                         bind uu____69203
                           (fun uu____69209  ->
                              mlog
                                (fun uu____69213  ->
                                   let uu____69214 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____69216 =
                                     let uu____69218 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____69218
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____69214 uu____69216)
                                (fun uu____69222  ->
                                   let uu____69223 =
                                     let uu____69227 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____69228 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____69227 typ uu____69228  in
                                   bind uu____69223
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____69238 =
                                             let uu____69240 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____69240 t1  in
                                           let uu____69241 =
                                             let uu____69243 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____69243 typ  in
                                           let uu____69244 =
                                             let uu____69246 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____69247 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____69246 uu____69247  in
                                           let uu____69248 =
                                             let uu____69250 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____69251 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____69250 uu____69251  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____69238 uu____69241
                                             uu____69244 uu____69248)))))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun try_refine  ->
    fun set_expected_typ1  ->
      fun tm  ->
        let uu____69277 =
          mlog
            (fun uu____69282  ->
               let uu____69283 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____69283)
            (fun uu____69288  ->
               let uu____69289 =
                 let uu____69296 = __exact_now set_expected_typ1 tm  in
                 catch uu____69296  in
               bind uu____69289
                 (fun uu___611_69305  ->
                    match uu___611_69305 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        traise e
                    | FStar_Util.Inl e ->
                        mlog
                          (fun uu____69316  ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____69320  ->
                             let uu____69321 =
                               let uu____69328 =
                                 let uu____69331 =
                                   norm [FStar_Syntax_Embeddings.Delta]  in
                                 bind uu____69331
                                   (fun uu____69336  ->
                                      let uu____69337 = refine_intro ()  in
                                      bind uu____69337
                                        (fun uu____69341  ->
                                           __exact_now set_expected_typ1 tm))
                                  in
                               catch uu____69328  in
                             bind uu____69321
                               (fun uu___610_69348  ->
                                  match uu___610_69348 with
                                  | FStar_Util.Inr r ->
                                      mlog
                                        (fun uu____69357  ->
                                           FStar_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu____69360  -> ret ())
                                  | FStar_Util.Inl uu____69361 ->
                                      mlog
                                        (fun uu____69363  ->
                                           FStar_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu____69366  -> traise e)))))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____69277
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____69418 = f x  in
          bind uu____69418
            (fun y  ->
               let uu____69426 = mapM f xs  in
               bind uu____69426 (fun ys  -> ret (y :: ys)))
  
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
          let uu____69498 = do_unify e ty1 ty2  in
          bind uu____69498
            (fun uu___612_69512  ->
               if uu___612_69512
               then ret acc
               else
                 (let uu____69532 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____69532 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____69553 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____69555 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____69553
                        uu____69555
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____69572 =
                        let uu____69574 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____69574  in
                      if uu____69572
                      then fail "Codomain is effectful"
                      else
                        (let uu____69598 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____69598
                           (fun uu____69625  ->
                              match uu____69625 with
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
      let uu____69715 =
        mlog
          (fun uu____69720  ->
             let uu____69721 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_apply: tm = %s\n" uu____69721)
          (fun uu____69726  ->
             let uu____69727 = cur_goal ()  in
             bind uu____69727
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____69735 = __tc e tm  in
                  bind uu____69735
                    (fun uu____69756  ->
                       match uu____69756 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____69769 =
                             let uu____69780 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____69780  in
                           bind uu____69769
                             (fun uvs  ->
                                let fix_qual q =
                                  match q with
                                  | FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Meta uu____69818)
                                      ->
                                      FStar_Pervasives_Native.Some
                                        (FStar_Syntax_Syntax.Implicit false)
                                  | uu____69822 -> q  in
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____69845  ->
                                       fun w  ->
                                         match uu____69845 with
                                         | (uvt,q,uu____69863) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, (fix_qual q))]) uvs tm1
                                   in
                                let uvset =
                                  let uu____69895 =
                                    FStar_Syntax_Free.new_uv_set ()  in
                                  FStar_List.fold_right
                                    (fun uu____69912  ->
                                       fun s  ->
                                         match uu____69912 with
                                         | (uu____69924,uu____69925,uv) ->
                                             let uu____69927 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                in
                                             FStar_Util.set_union s
                                               uu____69927) uvs uu____69895
                                   in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset  in
                                let uu____69937 = solve' goal w  in
                                bind uu____69937
                                  (fun uu____69942  ->
                                     let uu____69943 =
                                       mapM
                                         (fun uu____69960  ->
                                            match uu____69960 with
                                            | (uvt,q,uv) ->
                                                let uu____69972 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                   in
                                                (match uu____69972 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____69977 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____69978 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv)
                                                        in
                                                     if uu____69978
                                                     then ret ()
                                                     else
                                                       (let uu____69985 =
                                                          let uu____69988 =
                                                            bnorm_goal
                                                              (let uu___1452_69991
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___1452_69991.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___1452_69991.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false;
                                                                 FStar_Tactics_Types.label
                                                                   =
                                                                   (uu___1452_69991.FStar_Tactics_Types.label)
                                                               })
                                                             in
                                                          [uu____69988]  in
                                                        add_goals uu____69985)))
                                         uvs
                                        in
                                     bind uu____69943
                                       (fun uu____69996  ->
                                          proc_guard "apply guard" e guard))))))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____69715
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____70024 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____70024
    then
      let uu____70033 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____70048 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____70101 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____70033 with
      | (pre,post) ->
          let post1 =
            let uu____70134 =
              let uu____70145 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____70145]  in
            FStar_Syntax_Util.mk_app post uu____70134  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____70176 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____70176
       then
         let uu____70185 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____70185
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
            let uu____70264 = f x e  in
            bind uu____70264 (fun e'  -> fold_left f e' xs1)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____70279 =
      let uu____70282 =
        bind get
          (fun ps  ->
             mlog
               (fun uu____70289  ->
                  let uu____70290 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____70290)
               (fun uu____70296  ->
                  let is_unit_t t =
                    let uu____70304 =
                      let uu____70305 = FStar_Syntax_Subst.compress t  in
                      uu____70305.FStar_Syntax_Syntax.n  in
                    match uu____70304 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____70311 -> false  in
                  let uu____70313 = cur_goal ()  in
                  bind uu____70313
                    (fun goal  ->
                       let uu____70319 =
                         let uu____70328 = FStar_Tactics_Types.goal_env goal
                            in
                         __tc uu____70328 tm  in
                       bind uu____70319
                         (fun uu____70343  ->
                            match uu____70343 with
                            | (tm1,t,guard) ->
                                let uu____70355 =
                                  FStar_Syntax_Util.arrow_formals_comp t  in
                                (match uu____70355 with
                                 | (bs,comp) ->
                                     let uu____70388 = lemma_or_sq comp  in
                                     (match uu____70388 with
                                      | FStar_Pervasives_Native.None  ->
                                          fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre,post) ->
                                          let uu____70408 =
                                            fold_left
                                              (fun uu____70470  ->
                                                 fun uu____70471  ->
                                                   match (uu____70470,
                                                           uu____70471)
                                                   with
                                                   | ((b,aq),(uvs,imps,subst1))
                                                       ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst1
                                                           b.FStar_Syntax_Syntax.sort
                                                          in
                                                       let uu____70622 =
                                                         is_unit_t b_t  in
                                                       if uu____70622
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
                                                         (let uu____70745 =
                                                            let uu____70752 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            new_uvar
                                                              "apply_lemma"
                                                              uu____70752 b_t
                                                             in
                                                          bind uu____70745
                                                            (fun uu____70783 
                                                               ->
                                                               match uu____70783
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
                                          bind uu____70408
                                            (fun uu____70969  ->
                                               match uu____70969 with
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
                                                   let uu____71057 =
                                                     let uu____71061 =
                                                       FStar_Tactics_Types.goal_env
                                                         goal
                                                        in
                                                     let uu____71062 =
                                                       FStar_Syntax_Util.mk_squash
                                                         FStar_Syntax_Syntax.U_zero
                                                         post1
                                                        in
                                                     let uu____71063 =
                                                       FStar_Tactics_Types.goal_type
                                                         goal
                                                        in
                                                     do_unify uu____71061
                                                       uu____71062
                                                       uu____71063
                                                      in
                                                   bind uu____71057
                                                     (fun b  ->
                                                        if
                                                          Prims.op_Negation b
                                                        then
                                                          let uu____71074 =
                                                            let uu____71076 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            tts uu____71076
                                                              tm1
                                                             in
                                                          let uu____71077 =
                                                            let uu____71079 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            let uu____71080 =
                                                              FStar_Syntax_Util.mk_squash
                                                                FStar_Syntax_Syntax.U_zero
                                                                post1
                                                               in
                                                            tts uu____71079
                                                              uu____71080
                                                             in
                                                          let uu____71081 =
                                                            let uu____71083 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            let uu____71084 =
                                                              FStar_Tactics_Types.goal_type
                                                                goal
                                                               in
                                                            tts uu____71083
                                                              uu____71084
                                                             in
                                                          fail3
                                                            "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                            uu____71074
                                                            uu____71077
                                                            uu____71081
                                                        else
                                                          (let uu____71088 =
                                                             solve' goal
                                                               FStar_Syntax_Util.exp_unit
                                                              in
                                                           bind uu____71088
                                                             (fun uu____71096
                                                                 ->
                                                                let is_free_uvar
                                                                  uv t1 =
                                                                  let free_uvars
                                                                    =
                                                                    let uu____71122
                                                                    =
                                                                    let uu____71125
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____71125
                                                                     in
                                                                    FStar_List.map
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____71122
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
                                                                    let uu____71161
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____71161)
                                                                    goals
                                                                   in
                                                                let checkone
                                                                  t1 goals =
                                                                  let uu____71178
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                  match uu____71178
                                                                  with
                                                                  | (hd1,uu____71197)
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____71224)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____71241
                                                                    -> false)
                                                                   in
                                                                let uu____71243
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
                                                                    let uu____71286
                                                                    = imp  in
                                                                    match uu____71286
                                                                    with
                                                                    | 
                                                                    (term,ctx_uvar)
                                                                    ->
                                                                    let uu____71297
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____71297
                                                                    with
                                                                    | 
                                                                    (hd1,uu____71319)
                                                                    ->
                                                                    let uu____71344
                                                                    =
                                                                    let uu____71345
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____71345.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____71344
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____71353)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___1562_71373
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___1562_71373.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___1562_71373.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___1562_71373.FStar_Tactics_Types.is_guard);
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___1562_71373.FStar_Tactics_Types.label)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____71376
                                                                    ->
                                                                    mlog
                                                                    (fun
                                                                    uu____71382
                                                                     ->
                                                                    let uu____71383
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                                                     in
                                                                    let uu____71385
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____71383
                                                                    uu____71385)
                                                                    (fun
                                                                    uu____71392
                                                                     ->
                                                                    let env =
                                                                    let uu___1567_71394
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___1567_71394.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1567_71394.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1567_71394.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___1567_71394.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1567_71394.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1567_71394.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1567_71394.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1567_71394.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___1567_71394.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___1567_71394.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___1567_71394.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1567_71394.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1567_71394.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1567_71394.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1567_71394.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1567_71394.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1567_71394.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1567_71394.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___1567_71394.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___1567_71394.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___1567_71394.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1567_71394.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1567_71394.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1567_71394.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1567_71394.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1567_71394.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1567_71394.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1567_71394.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1567_71394.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1567_71394.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1567_71394.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1567_71394.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1567_71394.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1567_71394.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___1567_71394.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1567_71394.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1567_71394.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___1567_71394.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1567_71394.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1567_71394.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1567_71394.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1567_71394.FStar_TypeChecker_Env.nbe)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let uu____71397
                                                                    =
                                                                    let uu____71400
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____71404
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
                                                                    let uu____71406
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____71404
                                                                    uu____71406
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____71412
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    uu____71400
                                                                    uu____71412
                                                                    g_typ  in
                                                                    bind
                                                                    uu____71397
                                                                    (fun
                                                                    uu____71416
                                                                     ->
                                                                    ret []))))))
                                                                   in
                                                                bind
                                                                  uu____71243
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
                                                                    let uu____71480
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____71480
                                                                    then
                                                                    let uu____71485
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____71485
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
                                                                    let uu____71500
                                                                    =
                                                                    let uu____71502
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____71502
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____71500)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____71503
                                                                    =
                                                                    let uu____71506
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____71506
                                                                    guard  in
                                                                    bind
                                                                    uu____71503
                                                                    (fun
                                                                    uu____71510
                                                                     ->
                                                                    let uu____71511
                                                                    =
                                                                    let uu____71514
                                                                    =
                                                                    let uu____71516
                                                                    =
                                                                    let uu____71518
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____71519
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____71518
                                                                    uu____71519
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____71516
                                                                     in
                                                                    if
                                                                    uu____71514
                                                                    then
                                                                    let uu____71523
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____71523
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    goal.FStar_Tactics_Types.label
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____71511
                                                                    (fun
                                                                    uu____71528
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2)))))))))))))
         in
      focus uu____70282  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____70279
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____71552 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____71552 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____71562::(e1,uu____71564)::(e2,uu____71566)::[])) when
        (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) ||
          (FStar_Ident.lid_equals l FStar_Parser_Const.c_eq2_lid)
        -> FStar_Pervasives_Native.Some (e1, e2)
    | uu____71627 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____71652 = destruct_eq' typ  in
    match uu____71652 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____71682 = FStar_Syntax_Util.un_squash typ  in
        (match uu____71682 with
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
        let uu____71751 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____71751 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', bv', [])
            else
              (let uu____71809 = aux e'  in
               FStar_Util.map_opt uu____71809
                 (fun uu____71840  ->
                    match uu____71840 with
                    | (e'',bv,bvs) -> (e'', bv, (bv' :: bvs))))
         in
      let uu____71866 = aux e  in
      FStar_Util.map_opt uu____71866
        (fun uu____71897  ->
           match uu____71897 with
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
          let uu____71971 =
            let uu____71982 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____71982  in
          FStar_Util.map_opt uu____71971
            (fun uu____72000  ->
               match uu____72000 with
               | (e0,b11,bvs) ->
                   let s1 bv =
                     let uu___1640_72022 = bv  in
                     let uu____72023 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___1640_72022.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___1640_72022.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____72023
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___1644_72031 =
                       g.FStar_Tactics_Types.goal_ctx_uvar  in
                     let uu____72032 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____72041 =
                       let uu____72044 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____72044  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___1644_72031.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____72032;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____72041;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___1644_72031.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___1644_72031.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___1644_72031.FStar_Syntax_Syntax.ctx_uvar_range);
                       FStar_Syntax_Syntax.ctx_uvar_meta =
                         (uu___1644_72031.FStar_Syntax_Syntax.ctx_uvar_meta)
                     }  in
                   let uu___1647_72045 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1647_72045.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___1647_72045.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___1647_72045.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1647_72045.FStar_Tactics_Types.label)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____72056 =
      let uu____72059 = cur_goal ()  in
      bind uu____72059
        (fun goal  ->
           let uu____72067 = h  in
           match uu____72067 with
           | (bv,uu____72071) ->
               mlog
                 (fun uu____72079  ->
                    let uu____72080 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____72082 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____72080
                      uu____72082)
                 (fun uu____72087  ->
                    let uu____72088 =
                      let uu____72099 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____72099  in
                    match uu____72088 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                        let uu____72126 =
                          destruct_eq bv1.FStar_Syntax_Syntax.sort  in
                        (match uu____72126 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____72141 =
                               let uu____72142 =
                                 FStar_Syntax_Subst.compress x  in
                               uu____72142.FStar_Syntax_Syntax.n  in
                             (match uu____72141 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv2 =
                                    let uu___1670_72159 = bv2  in
                                    let uu____72160 =
                                      FStar_Syntax_Subst.subst s
                                        bv2.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1670_72159.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1670_72159.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____72160
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv1 :: bvs1)  in
                                  let new_goal =
                                    let uu___1674_72168 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____72169 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____72178 =
                                      let uu____72181 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____72181
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___1674_72168.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____72169;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____72178;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___1674_72168.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___1674_72168.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___1674_72168.FStar_Syntax_Syntax.ctx_uvar_range);
                                      FStar_Syntax_Syntax.ctx_uvar_meta =
                                        (uu___1674_72168.FStar_Syntax_Syntax.ctx_uvar_meta)
                                    }  in
                                  replace_cur
                                    (let uu___1677_72184 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___1677_72184.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___1677_72184.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___1677_72184.FStar_Tactics_Types.is_guard);
                                       FStar_Tactics_Types.label =
                                         (uu___1677_72184.FStar_Tactics_Types.label)
                                     })
                              | uu____72185 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____72187 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____72056
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____72217 =
        let uu____72220 = cur_goal ()  in
        bind uu____72220
          (fun goal  ->
             let uu____72231 = b  in
             match uu____72231 with
             | (bv,uu____72235) ->
                 let bv' =
                   let uu____72241 =
                     let uu___1688_72242 = bv  in
                     let uu____72243 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____72243;
                       FStar_Syntax_Syntax.index =
                         (uu___1688_72242.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___1688_72242.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____72241  in
                 let s1 =
                   let uu____72248 =
                     let uu____72249 =
                       let uu____72256 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____72256)  in
                     FStar_Syntax_Syntax.NT uu____72249  in
                   [uu____72248]  in
                 let uu____72261 = subst_goal bv bv' s1 goal  in
                 (match uu____72261 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____72217
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____72283 =
      let uu____72286 = cur_goal ()  in
      bind uu____72286
        (fun goal  ->
           let uu____72295 = b  in
           match uu____72295 with
           | (bv,uu____72299) ->
               let uu____72304 =
                 let uu____72315 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____72315  in
               (match uu____72304 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                    let uu____72342 = FStar_Syntax_Util.type_u ()  in
                    (match uu____72342 with
                     | (ty,u) ->
                         let uu____72351 = new_uvar "binder_retype" e0 ty  in
                         bind uu____72351
                           (fun uu____72370  ->
                              match uu____72370 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___1712_72380 = bv1  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1712_72380.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1712_72380.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____72384 =
                                      let uu____72385 =
                                        let uu____72392 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv1, uu____72392)  in
                                      FStar_Syntax_Syntax.NT uu____72385  in
                                    [uu____72384]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___1717_72404 = b1  in
                                         let uu____72405 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___1717_72404.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___1717_72404.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____72405
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____72412  ->
                                       let new_goal =
                                         let uu____72414 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____72415 =
                                           let uu____72416 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____72416
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____72414 uu____72415
                                          in
                                       let uu____72417 = add_goals [new_goal]
                                          in
                                       bind uu____72417
                                         (fun uu____72422  ->
                                            let uu____72423 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv1.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____72423
                                              goal.FStar_Tactics_Types.opts
                                              goal.FStar_Tactics_Types.label))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____72283
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____72449 =
        let uu____72452 = cur_goal ()  in
        bind uu____72452
          (fun goal  ->
             let uu____72461 = b  in
             match uu____72461 with
             | (bv,uu____72465) ->
                 let uu____72470 =
                   let uu____72481 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____72481  in
                 (match uu____72470 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                      let steps =
                        let uu____72511 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____72511
                         in
                      let sort' =
                        normalize steps e0 bv1.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___1738_72516 = bv1  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___1738_72516.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___1738_72516.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____72518 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____72518))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____72449
  
let (revert : unit -> unit tac) =
  fun uu____72531  ->
    let uu____72534 = cur_goal ()  in
    bind uu____72534
      (fun goal  ->
         let uu____72540 =
           let uu____72547 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____72547  in
         match uu____72540 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____72564 =
                 let uu____72567 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____72567  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____72564
                in
             let uu____72582 = new_uvar "revert" env' typ'  in
             bind uu____72582
               (fun uu____72598  ->
                  match uu____72598 with
                  | (r,u_r) ->
                      let uu____72607 =
                        let uu____72610 =
                          let uu____72611 =
                            let uu____72612 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____72612.FStar_Syntax_Syntax.pos  in
                          let uu____72615 =
                            let uu____72620 =
                              let uu____72621 =
                                let uu____72630 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____72630  in
                              [uu____72621]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____72620  in
                          uu____72615 FStar_Pervasives_Native.None
                            uu____72611
                           in
                        set_solution goal uu____72610  in
                      bind uu____72607
                        (fun uu____72649  ->
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
      let uu____72663 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____72663
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____72679 = cur_goal ()  in
    bind uu____72679
      (fun goal  ->
         mlog
           (fun uu____72687  ->
              let uu____72688 = FStar_Syntax_Print.binder_to_string b  in
              let uu____72690 =
                let uu____72692 =
                  let uu____72694 =
                    let uu____72703 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____72703  in
                  FStar_All.pipe_right uu____72694 FStar_List.length  in
                FStar_All.pipe_right uu____72692 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____72688 uu____72690)
           (fun uu____72724  ->
              let uu____72725 =
                let uu____72736 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____72736  in
              match uu____72725 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bv1,bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____72781 =
                          free_in bv1 bv'.FStar_Syntax_Syntax.sort  in
                        if uu____72781
                        then
                          let uu____72786 =
                            let uu____72788 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____72788
                             in
                          fail uu____72786
                        else check1 bvs2
                     in
                  let uu____72793 =
                    let uu____72795 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv1 uu____72795  in
                  if uu____72793
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____72802 = check1 bvs  in
                     bind uu____72802
                       (fun uu____72808  ->
                          let env' = push_bvs e' bvs  in
                          let uu____72810 =
                            let uu____72817 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____72817  in
                          bind uu____72810
                            (fun uu____72827  ->
                               match uu____72827 with
                               | (ut,uvar_ut) ->
                                   let uu____72836 = set_solution goal ut  in
                                   bind uu____72836
                                     (fun uu____72841  ->
                                        let uu____72842 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                            goal.FStar_Tactics_Types.label
                                           in
                                        replace_cur uu____72842))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____72850  ->
    let uu____72853 = cur_goal ()  in
    bind uu____72853
      (fun goal  ->
         let uu____72859 =
           let uu____72866 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____72866  in
         match uu____72859 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____72875) ->
             let uu____72880 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____72880)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____72893 = cur_goal ()  in
    bind uu____72893
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____72903 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____72903  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____72906  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____72919 = cur_goal ()  in
    bind uu____72919
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____72929 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____72929  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____72932  -> add_goals [g']))
  
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
            let uu____72973 = FStar_Syntax_Subst.compress t  in
            uu____72973.FStar_Syntax_Syntax.n  in
          let uu____72976 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___1922_72983 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___1922_72983.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___1922_72983.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____72976
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____73000 =
                   let uu____73001 = FStar_Syntax_Subst.compress t1  in
                   uu____73001.FStar_Syntax_Syntax.n  in
                 match uu____73000 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____73032 = ff hd1  in
                     bind uu____73032
                       (fun hd2  ->
                          let fa uu____73058 =
                            match uu____73058 with
                            | (a,q) ->
                                let uu____73079 = ff a  in
                                bind uu____73079 (fun a1  -> ret (a1, q))
                             in
                          let uu____73098 = mapM fa args  in
                          bind uu____73098
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____73180 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____73180 with
                      | (bs1,t') ->
                          let uu____73189 =
                            let uu____73192 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____73192 t'  in
                          bind uu____73189
                            (fun t''  ->
                               let uu____73196 =
                                 let uu____73197 =
                                   let uu____73216 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____73225 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____73216, uu____73225, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____73197  in
                               ret uu____73196))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____73300 = ff hd1  in
                     bind uu____73300
                       (fun hd2  ->
                          let ffb br =
                            let uu____73315 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____73315 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____73347 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____73347  in
                                let uu____73348 = ff1 e  in
                                bind uu____73348
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____73363 = mapM ffb brs  in
                          bind uu____73363
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____73407;
                          FStar_Syntax_Syntax.lbtyp = uu____73408;
                          FStar_Syntax_Syntax.lbeff = uu____73409;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____73411;
                          FStar_Syntax_Syntax.lbpos = uu____73412;_}::[]),e)
                     ->
                     let lb =
                       let uu____73440 =
                         let uu____73441 = FStar_Syntax_Subst.compress t1  in
                         uu____73441.FStar_Syntax_Syntax.n  in
                       match uu____73440 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____73445) -> lb
                       | uu____73461 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____73471 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____73471
                         (fun def1  ->
                            ret
                              (let uu___1875_73477 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1875_73477.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1875_73477.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1875_73477.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1875_73477.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1875_73477.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1875_73477.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____73478 = fflb lb  in
                     bind uu____73478
                       (fun lb1  ->
                          let uu____73488 =
                            let uu____73493 =
                              let uu____73494 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____73494]  in
                            FStar_Syntax_Subst.open_term uu____73493 e  in
                          match uu____73488 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____73524 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____73524  in
                              let uu____73525 = ff1 e1  in
                              bind uu____73525
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____73572 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____73572
                         (fun def  ->
                            ret
                              (let uu___1893_73578 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1893_73578.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1893_73578.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1893_73578.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1893_73578.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1893_73578.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1893_73578.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____73579 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____73579 with
                      | (lbs1,e1) ->
                          let uu____73594 = mapM fflb lbs1  in
                          bind uu____73594
                            (fun lbs2  ->
                               let uu____73606 = ff e1  in
                               bind uu____73606
                                 (fun e2  ->
                                    let uu____73614 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____73614 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____73685 = ff t2  in
                     bind uu____73685
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____73716 = ff t2  in
                     bind uu____73716
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____73723 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___1917_73730 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___1917_73730.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___1917_73730.FStar_Syntax_Syntax.vars)
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
              let uu____73777 =
                FStar_TypeChecker_TcTerm.tc_term
                  (let uu___1930_73786 = env  in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___1930_73786.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___1930_73786.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___1930_73786.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___1930_73786.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_sig =
                       (uu___1930_73786.FStar_TypeChecker_Env.gamma_sig);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___1930_73786.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___1930_73786.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___1930_73786.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___1930_73786.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.attrtab =
                       (uu___1930_73786.FStar_TypeChecker_Env.attrtab);
                     FStar_TypeChecker_Env.is_pattern =
                       (uu___1930_73786.FStar_TypeChecker_Env.is_pattern);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___1930_73786.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___1930_73786.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___1930_73786.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___1930_73786.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___1930_73786.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___1930_73786.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___1930_73786.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___1930_73786.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___1930_73786.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax = true;
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___1930_73786.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.phase1 =
                       (uu___1930_73786.FStar_TypeChecker_Env.phase1);
                     FStar_TypeChecker_Env.failhard =
                       (uu___1930_73786.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___1930_73786.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.uvar_subtyping =
                       (uu___1930_73786.FStar_TypeChecker_Env.uvar_subtyping);
                     FStar_TypeChecker_Env.tc_term =
                       (uu___1930_73786.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.type_of =
                       (uu___1930_73786.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___1930_73786.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.check_type_of =
                       (uu___1930_73786.FStar_TypeChecker_Env.check_type_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___1930_73786.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (uu___1930_73786.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (uu___1930_73786.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.fv_delta_depths =
                       (uu___1930_73786.FStar_TypeChecker_Env.fv_delta_depths);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___1930_73786.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (uu___1930_73786.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.splice =
                       (uu___1930_73786.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.postprocess =
                       (uu___1930_73786.FStar_TypeChecker_Env.postprocess);
                     FStar_TypeChecker_Env.is_native_tactic =
                       (uu___1930_73786.FStar_TypeChecker_Env.is_native_tactic);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___1930_73786.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (uu___1930_73786.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (uu___1930_73786.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.nbe =
                       (uu___1930_73786.FStar_TypeChecker_Env.nbe)
                   }) t
                 in
              match uu____73777 with
              | (t1,lcomp,g) ->
                  let uu____73793 =
                    (let uu____73797 =
                       FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                     Prims.op_Negation uu____73797) ||
                      (let uu____73800 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____73800)
                     in
                  if uu____73793
                  then ret t1
                  else
                    (let rewrite_eq =
                       let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                       let uu____73811 = new_uvar "pointwise_rec" env typ  in
                       bind uu____73811
                         (fun uu____73828  ->
                            match uu____73828 with
                            | (ut,uvar_ut) ->
                                (log ps
                                   (fun uu____73841  ->
                                      let uu____73842 =
                                        FStar_Syntax_Print.term_to_string t1
                                         in
                                      let uu____73844 =
                                        FStar_Syntax_Print.term_to_string ut
                                         in
                                      FStar_Util.print2
                                        "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                        uu____73842 uu____73844);
                                 (let uu____73847 =
                                    let uu____73850 =
                                      let uu____73851 =
                                        FStar_TypeChecker_TcTerm.universe_of
                                          env typ
                                         in
                                      FStar_Syntax_Util.mk_eq2 uu____73851
                                        typ t1 ut
                                       in
                                    add_irrelevant_goal
                                      "pointwise_rec equation" env
                                      uu____73850 opts label1
                                     in
                                  bind uu____73847
                                    (fun uu____73855  ->
                                       let uu____73856 =
                                         bind tau
                                           (fun uu____73862  ->
                                              let ut1 =
                                                FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                  env ut
                                                 in
                                              log ps
                                                (fun uu____73868  ->
                                                   let uu____73869 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1
                                                      in
                                                   let uu____73871 =
                                                     FStar_Syntax_Print.term_to_string
                                                       ut1
                                                      in
                                                   FStar_Util.print2
                                                     "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                     uu____73869 uu____73871);
                                              ret ut1)
                                          in
                                       focus uu____73856))))
                        in
                     let uu____73874 = catch rewrite_eq  in
                     bind uu____73874
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
          let uu____74086 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____74086
            (fun t1  ->
               let uu____74094 =
                 f env
                   (let uu___2007_74102 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___2007_74102.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___2007_74102.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____74094
                 (fun uu____74118  ->
                    match uu____74118 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____74141 =
                               let uu____74142 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____74142.FStar_Syntax_Syntax.n  in
                             match uu____74141 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____74179 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____74179
                                   (fun uu____74201  ->
                                      match uu____74201 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____74217 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____74217
                                            (fun uu____74241  ->
                                               match uu____74241 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___1987_74271 =
                                                         t3  in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___1987_74271.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___1987_74271.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____74313 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____74313 with
                                  | (bs1,t') ->
                                      let uu____74328 =
                                        let uu____74335 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____74335 ctrl1 t'
                                         in
                                      bind uu____74328
                                        (fun uu____74350  ->
                                           match uu____74350 with
                                           | (t'',ctrl2) ->
                                               let uu____74365 =
                                                 let uu____74372 =
                                                   let uu___2000_74375 = t4
                                                      in
                                                   let uu____74378 =
                                                     let uu____74379 =
                                                       let uu____74398 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____74407 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____74398,
                                                         uu____74407, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____74379
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____74378;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___2000_74375.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___2000_74375.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____74372, ctrl2)  in
                                               ret uu____74365))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____74460 -> ret (t3, ctrl1))))

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
              let uu____74506 = ctrl_tac_fold f env ctrl t  in
              bind uu____74506
                (fun uu____74527  ->
                   match uu____74527 with
                   | (t1,ctrl1) ->
                       let uu____74542 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____74542
                         (fun uu____74566  ->
                            match uu____74566 with
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
                let uu____74657 =
                  let uu____74665 =
                    add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                      opts label1
                     in
                  bind uu____74665
                    (fun uu____74676  ->
                       let uu____74677 = ctrl t1  in
                       bind uu____74677
                         (fun res  ->
                            let uu____74703 = trivial ()  in
                            bind uu____74703 (fun uu____74712  -> ret res)))
                   in
                bind uu____74657
                  (fun uu____74730  ->
                     match uu____74730 with
                     | (should_rewrite,ctrl1) ->
                         if Prims.op_Negation should_rewrite
                         then ret (t1, ctrl1)
                         else
                           (let uu____74759 =
                              FStar_TypeChecker_TcTerm.tc_term
                                (let uu___2037_74768 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___2037_74768.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___2037_74768.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___2037_74768.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___2037_74768.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___2037_74768.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___2037_74768.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___2037_74768.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___2037_74768.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___2037_74768.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___2037_74768.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___2037_74768.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___2037_74768.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___2037_74768.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___2037_74768.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___2037_74768.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___2037_74768.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___2037_74768.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___2037_74768.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___2037_74768.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___2037_74768.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___2037_74768.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___2037_74768.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___2037_74768.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___2037_74768.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___2037_74768.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___2037_74768.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___2037_74768.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___2037_74768.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___2037_74768.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___2037_74768.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___2037_74768.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___2037_74768.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___2037_74768.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___2037_74768.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___2037_74768.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___2037_74768.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___2037_74768.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___2037_74768.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___2037_74768.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___2037_74768.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___2037_74768.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___2037_74768.FStar_TypeChecker_Env.nbe)
                                 }) t1
                               in
                            match uu____74759 with
                            | (t2,lcomp,g) ->
                                let uu____74779 =
                                  (let uu____74783 =
                                     FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                       lcomp
                                      in
                                   Prims.op_Negation uu____74783) ||
                                    (let uu____74786 =
                                       FStar_TypeChecker_Env.is_trivial g  in
                                     Prims.op_Negation uu____74786)
                                   in
                                if uu____74779
                                then ret (t2, globalStop)
                                else
                                  (let typ =
                                     lcomp.FStar_Syntax_Syntax.res_typ  in
                                   let uu____74802 =
                                     new_uvar "pointwise_rec" env typ  in
                                   bind uu____74802
                                     (fun uu____74823  ->
                                        match uu____74823 with
                                        | (ut,uvar_ut) ->
                                            (log ps
                                               (fun uu____74840  ->
                                                  let uu____74841 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t2
                                                     in
                                                  let uu____74843 =
                                                    FStar_Syntax_Print.term_to_string
                                                      ut
                                                     in
                                                  FStar_Util.print2
                                                    "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                    uu____74841 uu____74843);
                                             (let uu____74846 =
                                                let uu____74849 =
                                                  let uu____74850 =
                                                    FStar_TypeChecker_TcTerm.universe_of
                                                      env typ
                                                     in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____74850 typ t2 ut
                                                   in
                                                add_irrelevant_goal
                                                  "rewrite_rec equation" env
                                                  uu____74849 opts label1
                                                 in
                                              bind uu____74846
                                                (fun uu____74858  ->
                                                   let uu____74859 =
                                                     bind rewriter
                                                       (fun uu____74873  ->
                                                          let ut1 =
                                                            FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                              env ut
                                                             in
                                                          log ps
                                                            (fun uu____74879 
                                                               ->
                                                               let uu____74880
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   t2
                                                                  in
                                                               let uu____74882
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   ut1
                                                                  in
                                                               FStar_Util.print2
                                                                 "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                                 uu____74880
                                                                 uu____74882);
                                                          ret (ut1, ctrl1))
                                                      in
                                                   focus uu____74859)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term -> (Prims.bool * FStar_BigInt.t) tac) ->
    unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____74927 =
        bind get
          (fun ps  ->
             let uu____74937 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____74937 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____74975  ->
                       let uu____74976 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____74976);
                  bind dismiss_all
                    (fun uu____74981  ->
                       let uu____74982 =
                         let uu____74989 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____74989
                           keepGoing gt1
                          in
                       bind uu____74982
                         (fun uu____74999  ->
                            match uu____74999 with
                            | (gt',uu____75007) ->
                                (log ps
                                   (fun uu____75011  ->
                                      let uu____75012 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____75012);
                                 (let uu____75015 = push_goals gs  in
                                  bind uu____75015
                                    (fun uu____75020  ->
                                       let uu____75021 =
                                         let uu____75024 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____75024]  in
                                       add_goals uu____75021)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____74927
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____75049 =
        bind get
          (fun ps  ->
             let uu____75059 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____75059 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____75097  ->
                       let uu____75098 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____75098);
                  bind dismiss_all
                    (fun uu____75103  ->
                       let uu____75104 =
                         let uu____75107 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____75107 gt1
                          in
                       bind uu____75104
                         (fun gt'  ->
                            log ps
                              (fun uu____75115  ->
                                 let uu____75116 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____75116);
                            (let uu____75119 = push_goals gs  in
                             bind uu____75119
                               (fun uu____75124  ->
                                  let uu____75125 =
                                    let uu____75128 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____75128]  in
                                  add_goals uu____75125))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____75049
  
let (trefl : unit -> unit tac) =
  fun uu____75141  ->
    let uu____75144 =
      let uu____75147 = cur_goal ()  in
      bind uu____75147
        (fun g  ->
           let uu____75165 =
             let uu____75170 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____75170  in
           match uu____75165 with
           | FStar_Pervasives_Native.Some t ->
               let uu____75178 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____75178 with
                | (hd1,args) ->
                    let uu____75217 =
                      let uu____75230 =
                        let uu____75231 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____75231.FStar_Syntax_Syntax.n  in
                      (uu____75230, args)  in
                    (match uu____75217 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____75245::(l,uu____75247)::(r,uu____75249)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____75296 =
                           let uu____75300 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____75300 l r  in
                         bind uu____75296
                           (fun b  ->
                              if b
                              then solve' g FStar_Syntax_Util.exp_unit
                              else
                                (let l1 =
                                   let uu____75311 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____75311 l
                                    in
                                 let r1 =
                                   let uu____75313 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____75313 r
                                    in
                                 let uu____75314 =
                                   let uu____75318 =
                                     FStar_Tactics_Types.goal_env g  in
                                   do_unify uu____75318 l1 r1  in
                                 bind uu____75314
                                   (fun b1  ->
                                      if b1
                                      then
                                        solve' g FStar_Syntax_Util.exp_unit
                                      else
                                        (let uu____75328 =
                                           let uu____75330 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____75330 l1  in
                                         let uu____75331 =
                                           let uu____75333 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____75333 r1  in
                                         fail2
                                           "not a trivial equality ((%s) vs (%s))"
                                           uu____75328 uu____75331))))
                     | (hd2,uu____75336) ->
                         let uu____75353 =
                           let uu____75355 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____75355 t  in
                         fail1 "trefl: not an equality (%s)" uu____75353))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____75144
  
let (dup : unit -> unit tac) =
  fun uu____75372  ->
    let uu____75375 = cur_goal ()  in
    bind uu____75375
      (fun g  ->
         let uu____75381 =
           let uu____75388 = FStar_Tactics_Types.goal_env g  in
           let uu____75389 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____75388 uu____75389  in
         bind uu____75381
           (fun uu____75399  ->
              match uu____75399 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___2129_75409 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___2129_75409.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___2129_75409.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___2129_75409.FStar_Tactics_Types.is_guard);
                      FStar_Tactics_Types.label =
                        (uu___2129_75409.FStar_Tactics_Types.label)
                    }  in
                  bind __dismiss
                    (fun uu____75412  ->
                       let uu____75413 =
                         let uu____75416 = FStar_Tactics_Types.goal_env g  in
                         let uu____75417 =
                           let uu____75418 =
                             let uu____75419 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____75420 =
                               FStar_Tactics_Types.goal_type g  in
                             FStar_TypeChecker_TcTerm.universe_of uu____75419
                               uu____75420
                              in
                           let uu____75421 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____75422 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____75418 uu____75421 u
                             uu____75422
                            in
                         add_irrelevant_goal "dup equation" uu____75416
                           uu____75417 g.FStar_Tactics_Types.opts
                           g.FStar_Tactics_Types.label
                          in
                       bind uu____75413
                         (fun uu____75426  ->
                            let uu____75427 = add_goals [g']  in
                            bind uu____75427 (fun uu____75431  -> ret ())))))
  
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
              let uu____75557 = f x y  in
              if uu____75557 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____75580 -> (acc, l11, l21)  in
        let uu____75595 = aux [] l1 l2  in
        match uu____75595 with | (pr,t1,t2) -> ((FStar_List.rev pr), t1, t2)
  
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
      let uu____75701 = get_phi g1  in
      match uu____75701 with
      | FStar_Pervasives_Native.None  -> fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____75708 = get_phi g2  in
          (match uu____75708 with
           | FStar_Pervasives_Native.None  -> fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let uu____75721 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2)
                  in
               (match uu____75721 with
                | (gamma,r1,r2) ->
                    let t1 =
                      let uu____75752 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1)
                         in
                      close_forall_no_univs1 uu____75752 phi1  in
                    let t2 =
                      let uu____75762 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2)
                         in
                      close_forall_no_univs1 uu____75762 phi2  in
                    let uu____75771 =
                      set_solution g1 FStar_Syntax_Util.exp_unit  in
                    bind uu____75771
                      (fun uu____75776  ->
                         let uu____75777 =
                           set_solution g2 FStar_Syntax_Util.exp_unit  in
                         bind uu____75777
                           (fun uu____75784  ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2  in
                              let nenv =
                                let uu___2180_75789 =
                                  FStar_Tactics_Types.goal_env g1  in
                                let uu____75790 =
                                  FStar_Util.smap_create
                                    (Prims.parse_int "100")
                                   in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___2180_75789.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___2180_75789.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___2180_75789.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___2180_75789.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____75790;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___2180_75789.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___2180_75789.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___2180_75789.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___2180_75789.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___2180_75789.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___2180_75789.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___2180_75789.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___2180_75789.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___2180_75789.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___2180_75789.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___2180_75789.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___2180_75789.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___2180_75789.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___2180_75789.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___2180_75789.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___2180_75789.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___2180_75789.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___2180_75789.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___2180_75789.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___2180_75789.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___2180_75789.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___2180_75789.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___2180_75789.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___2180_75789.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___2180_75789.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___2180_75789.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___2180_75789.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___2180_75789.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___2180_75789.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___2180_75789.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___2180_75789.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___2180_75789.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___2180_75789.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___2180_75789.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___2180_75789.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___2180_75789.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___2180_75789.FStar_TypeChecker_Env.nbe)
                                }  in
                              let uu____75794 =
                                mk_irrelevant_goal "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                  g1.FStar_Tactics_Types.label
                                 in
                              bind uu____75794
                                (fun goal  ->
                                   mlog
                                     (fun uu____75804  ->
                                        let uu____75805 =
                                          goal_to_string_verbose g1  in
                                        let uu____75807 =
                                          goal_to_string_verbose g2  in
                                        let uu____75809 =
                                          goal_to_string_verbose goal  in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____75805 uu____75807 uu____75809)
                                     (fun uu____75813  -> ret goal))))))
  
let (join : unit -> unit tac) =
  fun uu____75821  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____75837 =
               set
                 (let uu___2195_75842 = ps  in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___2195_75842.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.main_goal =
                      (uu___2195_75842.FStar_Tactics_Types.main_goal);
                    FStar_Tactics_Types.all_implicits =
                      (uu___2195_75842.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___2195_75842.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___2195_75842.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___2195_75842.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___2195_75842.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___2195_75842.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___2195_75842.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___2195_75842.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___2195_75842.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___2195_75842.FStar_Tactics_Types.local_state)
                  })
                in
             bind uu____75837
               (fun uu____75845  ->
                  let uu____75846 = join_goals g1 g2  in
                  bind uu____75846 (fun g12  -> add_goals [g12]))
         | uu____75851 -> fail "join: less than 2 goals")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) tac)
  =
  fun t  ->
    let uu____75873 =
      let uu____75880 = cur_goal ()  in
      bind uu____75880
        (fun g  ->
           let uu____75890 =
             let uu____75899 = FStar_Tactics_Types.goal_env g  in
             __tc uu____75899 t  in
           bind uu____75890
             (fun uu____75927  ->
                match uu____75927 with
                | (t1,typ,guard) ->
                    let uu____75943 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____75943 with
                     | (hd1,args) ->
                         let uu____75992 =
                           let uu____76007 =
                             let uu____76008 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____76008.FStar_Syntax_Syntax.n  in
                           (uu____76007, args)  in
                         (match uu____75992 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____76029)::(q,uu____76031)::[]) when
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
                                let uu____76085 =
                                  let uu____76086 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____76086
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____76085
                                 in
                              let g2 =
                                let uu____76088 =
                                  let uu____76089 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____76089
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____76088
                                 in
                              bind __dismiss
                                (fun uu____76096  ->
                                   let uu____76097 = add_goals [g1; g2]  in
                                   bind uu____76097
                                     (fun uu____76106  ->
                                        let uu____76107 =
                                          let uu____76112 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____76113 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____76112, uu____76113)  in
                                        ret uu____76107))
                          | uu____76118 ->
                              let uu____76133 =
                                let uu____76135 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____76135 typ  in
                              fail1 "Not a disjunction: %s" uu____76133))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____75873
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____76170 =
      let uu____76173 = cur_goal ()  in
      bind uu____76173
        (fun g  ->
           FStar_Options.push ();
           (let uu____76186 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____76186);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___2232_76193 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___2232_76193.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___2232_76193.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___2232_76193.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___2232_76193.FStar_Tactics_Types.label)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____76170
  
let (top_env : unit -> env tac) =
  fun uu____76210  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____76225  ->
    let uu____76229 = cur_goal ()  in
    bind uu____76229
      (fun g  ->
         let uu____76236 =
           (FStar_Options.lax ()) ||
             (let uu____76239 = FStar_Tactics_Types.goal_env g  in
              uu____76239.FStar_TypeChecker_Env.lax)
            in
         ret uu____76236)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____76256 =
        mlog
          (fun uu____76261  ->
             let uu____76262 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____76262)
          (fun uu____76267  ->
             let uu____76268 = cur_goal ()  in
             bind uu____76268
               (fun goal  ->
                  let env =
                    let uu____76276 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____76276 ty  in
                  let uu____76277 = __tc_ghost env tm  in
                  bind uu____76277
                    (fun uu____76296  ->
                       match uu____76296 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____76310  ->
                                let uu____76311 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____76311)
                             (fun uu____76315  ->
                                mlog
                                  (fun uu____76318  ->
                                     let uu____76319 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____76319)
                                  (fun uu____76324  ->
                                     let uu____76325 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____76325
                                       (fun uu____76330  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____76256
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____76355 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____76361 =
              let uu____76368 =
                let uu____76369 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____76369
                 in
              new_uvar "uvar_env.2" env uu____76368  in
            bind uu____76361
              (fun uu____76386  ->
                 match uu____76386 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____76355
        (fun typ  ->
           let uu____76398 = new_uvar "uvar_env" env typ  in
           bind uu____76398
             (fun uu____76413  ->
                match uu____76413 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____76432 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____76451 -> g.FStar_Tactics_Types.opts
             | uu____76454 -> FStar_Options.peek ()  in
           let uu____76457 = FStar_Syntax_Util.head_and_args t  in
           match uu____76457 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____76477);
                FStar_Syntax_Syntax.pos = uu____76478;
                FStar_Syntax_Syntax.vars = uu____76479;_},uu____76480)
               ->
               let env1 =
                 let uu___2286_76522 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___2286_76522.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___2286_76522.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___2286_76522.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___2286_76522.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___2286_76522.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___2286_76522.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___2286_76522.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___2286_76522.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___2286_76522.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___2286_76522.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___2286_76522.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___2286_76522.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___2286_76522.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___2286_76522.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___2286_76522.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___2286_76522.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___2286_76522.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___2286_76522.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___2286_76522.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___2286_76522.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___2286_76522.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___2286_76522.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___2286_76522.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___2286_76522.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___2286_76522.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___2286_76522.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___2286_76522.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___2286_76522.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___2286_76522.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___2286_76522.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___2286_76522.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___2286_76522.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___2286_76522.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___2286_76522.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___2286_76522.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___2286_76522.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___2286_76522.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___2286_76522.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___2286_76522.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___2286_76522.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___2286_76522.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___2286_76522.FStar_TypeChecker_Env.nbe)
                 }  in
               let g =
                 FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false ""  in
               let uu____76526 =
                 let uu____76529 = bnorm_goal g  in [uu____76529]  in
               add_goals uu____76526
           | uu____76530 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____76432
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____76592 = if b then t2 else ret false  in
             bind uu____76592 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____76618 = trytac comp  in
      bind uu____76618
        (fun uu___613_76630  ->
           match uu___613_76630 with
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
        let uu____76672 =
          bind get
            (fun ps  ->
               let uu____76680 = __tc e t1  in
               bind uu____76680
                 (fun uu____76701  ->
                    match uu____76701 with
                    | (t11,ty1,g1) ->
                        let uu____76714 = __tc e t2  in
                        bind uu____76714
                          (fun uu____76735  ->
                             match uu____76735 with
                             | (t21,ty2,g2) ->
                                 let uu____76748 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____76748
                                   (fun uu____76755  ->
                                      let uu____76756 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____76756
                                        (fun uu____76764  ->
                                           let uu____76765 =
                                             do_unify e ty1 ty2  in
                                           let uu____76769 =
                                             do_unify e t11 t21  in
                                           tac_and uu____76765 uu____76769)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____76672
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____76817  ->
             let uu____76818 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____76818
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
        (fun uu____76852  ->
           let uu____76853 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____76853)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____76864 =
      mlog
        (fun uu____76869  ->
           let uu____76870 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____76870)
        (fun uu____76875  ->
           let uu____76876 = cur_goal ()  in
           bind uu____76876
             (fun g  ->
                let uu____76882 =
                  let uu____76891 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____76891 ty  in
                bind uu____76882
                  (fun uu____76903  ->
                     match uu____76903 with
                     | (ty1,uu____76913,guard) ->
                         let uu____76915 =
                           let uu____76918 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____76918 guard  in
                         bind uu____76915
                           (fun uu____76922  ->
                              let uu____76923 =
                                let uu____76927 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____76928 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____76927 uu____76928 ty1  in
                              bind uu____76923
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____76937 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____76937
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops]  in
                                      let ng =
                                        let uu____76944 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____76945 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____76944
                                          uu____76945
                                         in
                                      let nty =
                                        let uu____76947 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____76947 ty1  in
                                      let uu____76948 =
                                        let uu____76952 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____76952 ng nty  in
                                      bind uu____76948
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____76961 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____76961
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____76864
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) Prims.list tac)
  =
  fun s_tm  ->
    let uu____77035 =
      let uu____77044 = cur_goal ()  in
      bind uu____77044
        (fun g  ->
           let uu____77056 =
             let uu____77065 = FStar_Tactics_Types.goal_env g  in
             __tc uu____77065 s_tm  in
           bind uu____77056
             (fun uu____77083  ->
                match uu____77083 with
                | (s_tm1,s_ty,guard) ->
                    let uu____77101 =
                      let uu____77104 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____77104 guard  in
                    bind uu____77101
                      (fun uu____77117  ->
                         let uu____77118 =
                           FStar_Syntax_Util.head_and_args' s_ty  in
                         match uu____77118 with
                         | (h,args) ->
                             let uu____77163 =
                               let uu____77170 =
                                 let uu____77171 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____77171.FStar_Syntax_Syntax.n  in
                               match uu____77170 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____77186;
                                      FStar_Syntax_Syntax.vars = uu____77187;_},us)
                                   -> ret (fv, us)
                               | uu____77197 -> fail "type is not an fv"  in
                             bind uu____77163
                               (fun uu____77218  ->
                                  match uu____77218 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____77234 =
                                        let uu____77237 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____77237 t_lid
                                         in
                                      (match uu____77234 with
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
                                                  (fun uu____77288  ->
                                                     let uu____77289 =
                                                       FStar_Syntax_Subst.open_term
                                                         t_ps t_ty
                                                        in
                                                     match uu____77289 with
                                                     | (t_ps1,t_ty1) ->
                                                         let uu____77304 =
                                                           mapM
                                                             (fun c_lid  ->
                                                                let uu____77332
                                                                  =
                                                                  let uu____77335
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                  FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____77335
                                                                    c_lid
                                                                   in
                                                                match uu____77332
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
                                                                    uu____77409
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
                                                                    let uu____77414
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____77414
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____77437
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____77437
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____77480
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs
                                                                     in
                                                                    (match uu____77480
                                                                    with
                                                                    | 
                                                                    (d_ps,bs1)
                                                                    ->
                                                                    let uu____77553
                                                                    =
                                                                    let uu____77555
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp  in
                                                                    Prims.op_Negation
                                                                    uu____77555
                                                                     in
                                                                    failwhen
                                                                    uu____77553
                                                                    "not total?"
                                                                    (fun
                                                                    uu____77574
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
                                                                    uu___614_77591
                                                                    =
                                                                    match uu___614_77591
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____77595)
                                                                    -> true
                                                                    | 
                                                                    uu____77598
                                                                    -> false
                                                                     in
                                                                    let uu____77602
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____77602
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
                                                                    uu____77736
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
                                                                    uu____77798
                                                                     ->
                                                                    match uu____77798
                                                                    with
                                                                    | 
                                                                    ((bv,uu____77818),
                                                                    (t,uu____77820))
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
                                                                    uu____77890
                                                                     ->
                                                                    match uu____77890
                                                                    with
                                                                    | 
                                                                    ((bv,uu____77917),
                                                                    (t,uu____77919))
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
                                                                    uu____77978
                                                                     ->
                                                                    match uu____77978
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
                                                                    let uu____78033
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___2450_78050
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___2450_78050.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___2450_78050.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___2450_78050.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___2450_78050.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___2450_78050.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___2450_78050.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___2450_78050.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___2450_78050.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___2450_78050.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___2450_78050.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___2450_78050.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___2450_78050.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___2450_78050.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___2450_78050.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___2450_78050.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___2450_78050.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___2450_78050.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___2450_78050.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___2450_78050.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___2450_78050.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___2450_78050.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___2450_78050.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___2450_78050.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___2450_78050.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___2450_78050.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___2450_78050.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___2450_78050.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___2450_78050.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___2450_78050.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___2450_78050.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___2450_78050.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___2450_78050.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___2450_78050.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___2450_78050.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___2450_78050.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___2450_78050.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___2450_78050.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___2450_78050.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___2450_78050.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___2450_78050.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___2450_78050.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___2450_78050.FStar_TypeChecker_Env.nbe)
                                                                    }) s_ty
                                                                    pat  in
                                                                    match uu____78033
                                                                    with
                                                                    | 
                                                                    (uu____78064,uu____78065,uu____78066,pat_t,uu____78068,_guard_pat)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____78075
                                                                    =
                                                                    let uu____78076
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____78076
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____78075
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____78081
                                                                    =
                                                                    let uu____78090
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____78090]
                                                                     in
                                                                    let uu____78109
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____78081
                                                                    uu____78109
                                                                     in
                                                                    let nty =
                                                                    let uu____78115
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____78115
                                                                     in
                                                                    let uu____78118
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____78118
                                                                    (fun
                                                                    uu____78148
                                                                     ->
                                                                    match uu____78148
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
                                                                    let uu____78175
                                                                    =
                                                                    let uu____78186
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____78186]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____78175
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____78222
                                                                    =
                                                                    let uu____78233
                                                                    =
                                                                    let uu____78238
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2)  in
                                                                    (fv1,
                                                                    uu____78238)
                                                                     in
                                                                    (g', br,
                                                                    uu____78233)
                                                                     in
                                                                    ret
                                                                    uu____78222))))))
                                                                    | 
                                                                    uu____78259
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                             c_lids
                                                            in
                                                         bind uu____77304
                                                           (fun goal_brs  ->
                                                              let uu____78309
                                                                =
                                                                FStar_List.unzip3
                                                                  goal_brs
                                                                 in
                                                              match uu____78309
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
                                                                  let uu____78382
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                  bind
                                                                    uu____78382
                                                                    (
                                                                    fun
                                                                    uu____78393
                                                                     ->
                                                                    let uu____78394
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____78394
                                                                    (fun
                                                                    uu____78404
                                                                     ->
                                                                    ret infos))))
                                            | uu____78411 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____77035
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____78460::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____78490 = init xs  in x :: uu____78490
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____78503 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      let t3 = FStar_Syntax_Util.unlazy_emb t2  in
      match t3.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____78512) -> inspect t4
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____78578 = last args  in
          (match uu____78578 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____78608 =
                 let uu____78609 =
                   let uu____78614 =
                     let uu____78615 =
                       let uu____78620 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____78620  in
                     uu____78615 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____78614, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____78609  in
               FStar_All.pipe_left ret uu____78608)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____78631,uu____78632) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
          let uu____78685 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____78685 with
           | (bs1,t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____78727 =
                      let uu____78728 =
                        let uu____78733 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____78733)  in
                      FStar_Reflection_Data.Tv_Abs uu____78728  in
                    FStar_All.pipe_left ret uu____78727))
      | FStar_Syntax_Syntax.Tm_type uu____78736 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____78761 ->
          let uu____78776 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____78776 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____78807 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____78807 with
           | (b',t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____78860 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____78873 =
            let uu____78874 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____78874  in
          FStar_All.pipe_left ret uu____78873
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____78895 =
            let uu____78896 =
              let uu____78901 =
                let uu____78902 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____78902  in
              (uu____78901, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____78896  in
          FStar_All.pipe_left ret uu____78895
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____78942 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____78947 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____78947 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____79000 ->
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
             | FStar_Util.Inr uu____79042 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____79046 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____79046 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____79066 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____79072 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____79127 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____79127
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____79148 =
                  let uu____79155 =
                    FStar_List.map
                      (fun uu____79168  ->
                         match uu____79168 with
                         | (p1,uu____79177) -> inspect_pat p1) ps
                     in
                  (fv, uu____79155)  in
                FStar_Reflection_Data.Pat_Cons uu____79148
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
              (fun uu___615_79273  ->
                 match uu___615_79273 with
                 | (pat,uu____79295,t5) ->
                     let uu____79313 = inspect_pat pat  in (uu____79313, t5))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____79322 ->
          ((let uu____79324 =
              let uu____79330 =
                let uu____79332 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____79334 = FStar_Syntax_Print.term_to_string t3  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____79332 uu____79334
                 in
              (FStar_Errors.Warning_CantInspect, uu____79330)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____79324);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____78503
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____79352 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____79352
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____79356 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____79356
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____79360 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____79360
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____79367 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____79367
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____79392 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____79392
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____79409 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____79409
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____79428 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____79428
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____79432 =
          let uu____79433 =
            let uu____79440 =
              let uu____79441 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____79441  in
            FStar_Syntax_Syntax.mk uu____79440  in
          uu____79433 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____79432
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____79446 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____79446
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____79457 =
          let uu____79458 =
            let uu____79465 =
              let uu____79466 =
                let uu____79480 =
                  let uu____79483 =
                    let uu____79484 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____79484]  in
                  FStar_Syntax_Subst.close uu____79483 t2  in
                ((false, [lb]), uu____79480)  in
              FStar_Syntax_Syntax.Tm_let uu____79466  in
            FStar_Syntax_Syntax.mk uu____79465  in
          uu____79458 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____79457
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____79526 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____79526 with
         | (lbs,body) ->
             let uu____79541 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____79541)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____79578 =
                let uu____79579 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____79579  in
              FStar_All.pipe_left wrap uu____79578
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____79586 =
                let uu____79587 =
                  let uu____79601 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____79619 = pack_pat p1  in
                         (uu____79619, false)) ps
                     in
                  (fv, uu____79601)  in
                FStar_Syntax_Syntax.Pat_cons uu____79587  in
              FStar_All.pipe_left wrap uu____79586
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
            (fun uu___616_79668  ->
               match uu___616_79668 with
               | (pat,t1) ->
                   let uu____79685 = pack_pat pat  in
                   (uu____79685, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____79733 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____79733
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____79761 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____79761
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____79807 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____79807
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____79846 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____79846
  
let (lget :
  FStar_Reflection_Data.typ -> Prims.string -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun k  ->
      let uu____79866 =
        bind get
          (fun ps  ->
             let uu____79872 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____79872 with
             | FStar_Pervasives_Native.None  -> fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
      FStar_All.pipe_left (wrap_err "lget") uu____79866
  
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit tac)
  =
  fun _ty  ->
    fun k  ->
      fun t  ->
        let uu____79906 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___2748_79913 = ps  in
                 let uu____79914 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t
                    in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___2748_79913.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___2748_79913.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___2748_79913.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___2748_79913.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___2748_79913.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___2748_79913.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___2748_79913.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___2748_79913.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___2748_79913.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___2748_79913.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___2748_79913.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___2748_79913.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____79914
                 }  in
               set ps1)
           in
        FStar_All.pipe_left (wrap_err "lset") uu____79906
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal * FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun typ  ->
      let uu____79941 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____79941 with
      | (u,ctx_uvars,g_u) ->
          let uu____79974 = FStar_List.hd ctx_uvars  in
          (match uu____79974 with
           | (ctx_uvar,uu____79988) ->
               let g =
                 let uu____79990 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____79990 false
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
        let uu____80013 = goal_of_goal_ty env typ  in
        match uu____80013 with
        | (g,g_u) ->
            let ps =
              let uu____80025 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "TacVerbose")
                 in
              let uu____80028 = FStar_Util.psmap_empty ()  in
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
                FStar_Tactics_Types.tac_verb_dbg = uu____80025;
                FStar_Tactics_Types.local_state = uu____80028
              }  in
            let uu____80038 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____80038)
  