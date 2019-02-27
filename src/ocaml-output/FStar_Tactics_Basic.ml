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
    let uu____68717 =
      let uu____68718 = FStar_Tactics_Types.goal_env g  in
      let uu____68719 = FStar_Tactics_Types.goal_type g  in
      bnorm uu____68718 uu____68719  in
    FStar_Tactics_Types.goal_with_type g uu____68717
  
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
      let uu____68833 = FStar_Options.tactics_failhard ()  in
      if uu____68833
      then run t p
      else
        (try (fun uu___640_68843  -> match () with | () -> run t p) ()
         with
         | FStar_Errors.Err (uu____68852,msg) ->
             FStar_Tactics_Result.Failed
               ((FStar_Tactics_Types.TacticFailure msg), p)
         | FStar_Errors.Error (uu____68856,msg,uu____68858) ->
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
           let uu____68938 = run t1 p  in
           match uu____68938 with
           | FStar_Tactics_Result.Success (a,q) ->
               let uu____68945 = t2 a  in run uu____68945 q
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
    let uu____68968 =
      FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head  in
    match uu____68968 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (check_goal_solved :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun goal  -> get_uvar_solved goal.FStar_Tactics_Types.goal_ctx_uvar 
let (goal_to_string_verbose : FStar_Tactics_Types.goal -> Prims.string) =
  fun g  ->
    let uu____68990 =
      FStar_Syntax_Print.ctx_uvar_to_string
        g.FStar_Tactics_Types.goal_ctx_uvar
       in
    let uu____68992 =
      let uu____68994 = check_goal_solved g  in
      match uu____68994 with
      | FStar_Pervasives_Native.None  -> ""
      | FStar_Pervasives_Native.Some t ->
          let uu____69000 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "\tGOAL ALREADY SOLVED!: %s" uu____69000
       in
    FStar_Util.format2 "%s%s\n" uu____68990 uu____68992
  
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
            let uu____69047 = FStar_Options.print_implicits ()  in
            if uu____69047
            then
              let uu____69051 = FStar_Tactics_Types.goal_env g  in
              let uu____69052 = FStar_Tactics_Types.goal_witness g  in
              tts uu____69051 uu____69052
            else
              (let uu____69055 =
                 get_uvar_solved g.FStar_Tactics_Types.goal_ctx_uvar  in
               match uu____69055 with
               | FStar_Pervasives_Native.None  -> "_"
               | FStar_Pervasives_Native.Some t ->
                   let uu____69061 = FStar_Tactics_Types.goal_env g  in
                   let uu____69062 = FStar_Tactics_Types.goal_witness g  in
                   tts uu____69061 uu____69062)
             in
          let num =
            match maybe_num with
            | FStar_Pervasives_Native.None  -> ""
            | FStar_Pervasives_Native.Some (i,n1) ->
                let uu____69085 = FStar_Util.string_of_int i  in
                let uu____69087 = FStar_Util.string_of_int n1  in
                FStar_Util.format2 " %s/%s" uu____69085 uu____69087
             in
          let maybe_label =
            match g.FStar_Tactics_Types.label with
            | "" -> ""
            | l -> Prims.op_Hat " (" (Prims.op_Hat l ")")  in
          let actual_goal =
            if ps.FStar_Tactics_Types.tac_verb_dbg
            then goal_to_string_verbose g
            else
              (let uu____69105 =
                 FStar_Syntax_Print.binders_to_string ", "
                   (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
                  in
               let uu____69108 =
                 let uu____69110 = FStar_Tactics_Types.goal_env g  in
                 tts uu____69110
                   (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                  in
               FStar_Util.format3 "%s |- %s : %s\n" uu____69105 w uu____69108)
             in
          FStar_Util.format4 "%s%s%s:\n%s\n" kind num maybe_label actual_goal
  
let (tacprint : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      let uu____69137 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____69137
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____69162 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____69162
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____69194 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____69194
  
let (comp_to_typ : FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____69204) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____69214) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (get_phi :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun g  ->
    let uu____69234 =
      let uu____69235 = FStar_Tactics_Types.goal_env g  in
      let uu____69236 = FStar_Tactics_Types.goal_type g  in
      FStar_TypeChecker_Normalize.unfold_whnf uu____69235 uu____69236  in
    FStar_Syntax_Util.un_squash uu____69234
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  -> let uu____69245 = get_phi g  in FStar_Option.isSome uu____69245 
let (print : Prims.string -> unit tac) = fun msg  -> tacprint msg; ret () 
let (debugging : unit -> Prims.bool tac) =
  fun uu____69269  ->
    bind get
      (fun ps  ->
         let uu____69277 =
           FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
             (FStar_Options.Other "Tac")
            in
         ret uu____69277)
  
let (ps_to_string :
  (Prims.string * FStar_Tactics_Types.proofstate) -> Prims.string) =
  fun uu____69292  ->
    match uu____69292 with
    | (msg,ps) ->
        let p_imp imp =
          FStar_Syntax_Print.uvar_to_string
            (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
           in
        let n_active = FStar_List.length ps.FStar_Tactics_Types.goals  in
        let n_smt = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
        let n1 = n_active + n_smt  in
        let uu____69324 =
          let uu____69328 =
            let uu____69332 =
              let uu____69334 =
                FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
              FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____69334
                msg
               in
            let uu____69337 =
              let uu____69341 =
                if
                  ps.FStar_Tactics_Types.entry_range <>
                    FStar_Range.dummyRange
                then
                  let uu____69345 =
                    FStar_Range.string_of_def_range
                      ps.FStar_Tactics_Types.entry_range
                     in
                  FStar_Util.format1 "Location: %s\n" uu____69345
                else ""  in
              let uu____69351 =
                let uu____69355 =
                  let uu____69357 =
                    FStar_TypeChecker_Env.debug
                      ps.FStar_Tactics_Types.main_context
                      (FStar_Options.Other "Imp")
                     in
                  if uu____69357
                  then
                    let uu____69362 =
                      FStar_Common.string_of_list p_imp
                        ps.FStar_Tactics_Types.all_implicits
                       in
                    FStar_Util.format1 "Imps: %s\n" uu____69362
                  else ""  in
                [uu____69355]  in
              uu____69341 :: uu____69351  in
            uu____69332 :: uu____69337  in
          let uu____69372 =
            let uu____69376 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "Goal"
                       (FStar_Pervasives_Native.Some
                          (((Prims.parse_int "1") + i), n1)) ps g)
                ps.FStar_Tactics_Types.goals
               in
            let uu____69396 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "SMT Goal"
                       (FStar_Pervasives_Native.Some
                          ((((Prims.parse_int "1") + n_active) + i), n1)) ps
                       g) ps.FStar_Tactics_Types.smt_goals
               in
            FStar_List.append uu____69376 uu____69396  in
          FStar_List.append uu____69328 uu____69372  in
        FStar_String.concat "" uu____69324
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      let uu____69430 =
        let uu____69431 = FStar_Tactics_Types.goal_env g  in
        FStar_TypeChecker_Env.all_binders uu____69431  in
      let uu____69432 =
        let uu____69437 =
          let uu____69438 = FStar_Tactics_Types.goal_env g  in
          FStar_TypeChecker_Env.dsenv uu____69438  in
        FStar_Syntax_Print.binders_to_json uu____69437  in
      FStar_All.pipe_right uu____69430 uu____69432  in
    let uu____69439 =
      let uu____69447 =
        let uu____69455 =
          let uu____69461 =
            let uu____69462 =
              let uu____69470 =
                let uu____69476 =
                  let uu____69477 =
                    let uu____69479 = FStar_Tactics_Types.goal_env g  in
                    let uu____69480 = FStar_Tactics_Types.goal_witness g  in
                    tts uu____69479 uu____69480  in
                  FStar_Util.JsonStr uu____69477  in
                ("witness", uu____69476)  in
              let uu____69483 =
                let uu____69491 =
                  let uu____69497 =
                    let uu____69498 =
                      let uu____69500 = FStar_Tactics_Types.goal_env g  in
                      let uu____69501 = FStar_Tactics_Types.goal_type g  in
                      tts uu____69500 uu____69501  in
                    FStar_Util.JsonStr uu____69498  in
                  ("type", uu____69497)  in
                [uu____69491;
                ("label", (FStar_Util.JsonStr (g.FStar_Tactics_Types.label)))]
                 in
              uu____69470 :: uu____69483  in
            FStar_Util.JsonAssoc uu____69462  in
          ("goal", uu____69461)  in
        [uu____69455]  in
      ("hyps", g_binders) :: uu____69447  in
    FStar_Util.JsonAssoc uu____69439
  
let (ps_to_json :
  (Prims.string * FStar_Tactics_Types.proofstate) -> FStar_Util.json) =
  fun uu____69555  ->
    match uu____69555 with
    | (msg,ps) ->
        let uu____69565 =
          let uu____69573 =
            let uu____69581 =
              let uu____69589 =
                let uu____69597 =
                  let uu____69603 =
                    let uu____69604 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____69604  in
                  ("goals", uu____69603)  in
                let uu____69609 =
                  let uu____69617 =
                    let uu____69623 =
                      let uu____69624 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____69624  in
                    ("smt-goals", uu____69623)  in
                  [uu____69617]  in
                uu____69597 :: uu____69609  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____69589
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____69581  in
          let uu____69658 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____69674 =
                let uu____69680 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____69680)  in
              [uu____69674]
            else []  in
          FStar_List.append uu____69573 uu____69658  in
        FStar_Util.JsonAssoc uu____69565
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____69720  ->
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
         (let uu____69751 = FStar_Tactics_Types.subst_proof_state subst1 ps
             in
          dump_proofstate uu____69751 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let traise : 'a . Prims.exn -> 'a tac =
  fun e  -> mk_tac (fun ps  -> FStar_Tactics_Result.Failed (e, ps)) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____69824 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____69824
          then dump_proofstate ps (Prims.op_Hat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed
           ((FStar_Tactics_Types.TacticFailure msg), ps))
  
let fail1 : 'Auu____69838 . Prims.string -> Prims.string -> 'Auu____69838 tac
  =
  fun msg  ->
    fun x  -> let uu____69855 = FStar_Util.format1 msg x  in fail uu____69855
  
let fail2 :
  'Auu____69866 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____69866 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        let uu____69890 = FStar_Util.format2 msg x y  in fail uu____69890
  
let fail3 :
  'Auu____69903 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____69903 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____69934 = FStar_Util.format3 msg x y z  in fail uu____69934
  
let fail4 :
  'Auu____69949 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____69949 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____69987 = FStar_Util.format4 msg x y z w  in
            fail uu____69987
  
let catch : 'a . 'a tac -> (Prims.exn,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____70022 = run t ps  in
         match uu____70022 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___802_70046 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___802_70046.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___802_70046.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___802_70046.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___802_70046.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___802_70046.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___802_70046.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___802_70046.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___802_70046.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___802_70046.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___802_70046.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___802_70046.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (uu___802_70046.FStar_Tactics_Types.local_state)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let recover : 'a . 'a tac -> (Prims.exn,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let uu____70085 = run t ps  in
         match uu____70085 with
         | FStar_Tactics_Result.Success (a,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inr a), q)
         | FStar_Tactics_Result.Failed (m,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inl m), q))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____70133 = catch t  in
    bind uu____70133
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____70160 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try
           (fun uu___828_70192  ->
              match () with
              | () -> let uu____70197 = trytac t  in run uu____70197 ps) ()
         with
         | FStar_Errors.Err (uu____70213,msg) ->
             (log ps
                (fun uu____70219  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____70225,msg,uu____70227) ->
             (log ps
                (fun uu____70232  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____70269 = run t ps  in
           match uu____70269 with
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
  fun p  -> mk_tac (fun uu____70293  -> FStar_Tactics_Result.Success ((), p)) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___863_70308 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___863_70308.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___863_70308.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___863_70308.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___863_70308.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___863_70308.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___863_70308.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___863_70308.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___863_70308.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___863_70308.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___863_70308.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___863_70308.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___863_70308.FStar_Tactics_Types.local_state)
            }))
  
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____70332 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____70332
         then
           let uu____70336 = FStar_Syntax_Print.term_to_string t1  in
           let uu____70338 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____70336
             uu____70338
         else ());
        (try
           (fun uu___871_70349  ->
              match () with
              | () ->
                  let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
                  ((let uu____70357 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____70357
                    then
                      let uu____70361 =
                        FStar_Common.string_of_option
                          (FStar_TypeChecker_Rel.guard_to_string env) res
                         in
                      let uu____70363 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____70365 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.print3
                        "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____70361
                        uu____70363 uu____70365
                    else ());
                   (match res with
                    | FStar_Pervasives_Native.None  -> ret false
                    | FStar_Pervasives_Native.Some g ->
                        let uu____70376 =
                          add_implicits g.FStar_TypeChecker_Env.implicits  in
                        bind uu____70376 (fun uu____70381  -> ret true)))) ()
         with
         | FStar_Errors.Err (uu____70391,msg) ->
             mlog
               (fun uu____70397  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____70400  -> ret false)
         | FStar_Errors.Error (uu____70403,msg,r) ->
             mlog
               (fun uu____70411  ->
                  let uu____70412 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____70412) (fun uu____70416  -> ret false))
  
let (compress_implicits : unit tac) =
  bind get
    (fun ps  ->
       let imps = ps.FStar_Tactics_Types.all_implicits  in
       let g =
         let uu___897_70430 = FStar_TypeChecker_Env.trivial_guard  in
         {
           FStar_TypeChecker_Env.guard_f =
             (uu___897_70430.FStar_TypeChecker_Env.guard_f);
           FStar_TypeChecker_Env.deferred =
             (uu___897_70430.FStar_TypeChecker_Env.deferred);
           FStar_TypeChecker_Env.univ_ineqs =
             (uu___897_70430.FStar_TypeChecker_Env.univ_ineqs);
           FStar_TypeChecker_Env.implicits = imps
         }  in
       let g1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g
          in
       let ps' =
         let uu___901_70433 = ps  in
         {
           FStar_Tactics_Types.main_context =
             (uu___901_70433.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___901_70433.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (g1.FStar_TypeChecker_Env.implicits);
           FStar_Tactics_Types.goals =
             (uu___901_70433.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___901_70433.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___901_70433.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___901_70433.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___901_70433.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___901_70433.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___901_70433.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___901_70433.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___901_70433.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___901_70433.FStar_Tactics_Types.local_state)
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
          (fun uu____70460  ->
             (let uu____70462 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____70462
              then
                (FStar_Options.push ();
                 (let uu____70467 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____70471 = __do_unify env t1 t2  in
              bind uu____70471
                (fun r  ->
                   (let uu____70482 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____70482 then FStar_Options.pop () else ());
                   ret r)))
  
let (remove_solved_goals : unit tac) =
  bind get
    (fun ps  ->
       let ps' =
         let uu___916_70496 = ps  in
         let uu____70497 =
           FStar_List.filter
             (fun g  ->
                let uu____70503 = check_goal_solved g  in
                FStar_Option.isNone uu____70503) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___916_70496.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___916_70496.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___916_70496.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____70497;
           FStar_Tactics_Types.smt_goals =
             (uu___916_70496.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___916_70496.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___916_70496.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___916_70496.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___916_70496.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___916_70496.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___916_70496.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___916_70496.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___916_70496.FStar_Tactics_Types.local_state)
         }  in
       set ps')
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____70521 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____70521 with
      | FStar_Pervasives_Native.Some uu____70526 ->
          let uu____70527 =
            let uu____70529 = goal_to_string_verbose goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____70529  in
          fail uu____70527
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____70550 = FStar_Tactics_Types.goal_env goal  in
      let uu____70551 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____70550 solution uu____70551
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____70558 =
         let uu___929_70559 = p  in
         let uu____70560 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___929_70559.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___929_70559.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___929_70559.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____70560;
           FStar_Tactics_Types.smt_goals =
             (uu___929_70559.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___929_70559.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___929_70559.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___929_70559.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___929_70559.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___929_70559.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___929_70559.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___929_70559.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___929_70559.FStar_Tactics_Types.local_state)
         }  in
       set uu____70558)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      mlog
        (fun uu____70582  ->
           let uu____70583 =
             let uu____70585 = FStar_Tactics_Types.goal_witness goal  in
             FStar_Syntax_Print.term_to_string uu____70585  in
           let uu____70586 = FStar_Syntax_Print.term_to_string solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____70583 uu____70586)
        (fun uu____70591  ->
           let uu____70592 = trysolve goal solution  in
           bind uu____70592
             (fun b  ->
                if b
                then bind __dismiss (fun uu____70604  -> remove_solved_goals)
                else
                  (let uu____70607 =
                     let uu____70609 =
                       let uu____70611 = FStar_Tactics_Types.goal_env goal
                          in
                       tts uu____70611 solution  in
                     let uu____70612 =
                       let uu____70614 = FStar_Tactics_Types.goal_env goal
                          in
                       let uu____70615 =
                         FStar_Tactics_Types.goal_witness goal  in
                       tts uu____70614 uu____70615  in
                     let uu____70616 =
                       let uu____70618 = FStar_Tactics_Types.goal_env goal
                          in
                       let uu____70619 = FStar_Tactics_Types.goal_type goal
                          in
                       tts uu____70618 uu____70619  in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____70609 uu____70612 uu____70616
                      in
                   fail uu____70607)))
  
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____70636 = set_solution goal solution  in
      bind uu____70636
        (fun uu____70640  ->
           bind __dismiss (fun uu____70642  -> remove_solved_goals))
  
let (set_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___945_70661 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___945_70661.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___945_70661.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___945_70661.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals = gs;
              FStar_Tactics_Types.smt_goals =
                (uu___945_70661.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___945_70661.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___945_70661.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___945_70661.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___945_70661.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___945_70661.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___945_70661.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___945_70661.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___945_70661.FStar_Tactics_Types.local_state)
            }))
  
let (set_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___949_70680 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___949_70680.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___949_70680.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___949_70680.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___949_70680.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals = gs;
              FStar_Tactics_Types.depth =
                (uu___949_70680.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___949_70680.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___949_70680.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___949_70680.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___949_70680.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___949_70680.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___949_70680.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___949_70680.FStar_Tactics_Types.local_state)
            }))
  
let (dismiss_all : unit tac) = set_goals [] 
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____70707 = FStar_Options.defensive ()  in
    if uu____70707
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____70717 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____70717)
         in
      let b2 =
        b1 &&
          (let uu____70721 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____70721)
         in
      let rec aux b3 e =
        let uu____70736 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____70736 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____70756 =
        (let uu____70760 = aux b2 env  in Prims.op_Negation uu____70760) &&
          (let uu____70763 = FStar_ST.op_Bang nwarn  in
           uu____70763 < (Prims.parse_int "5"))
         in
      (if uu____70756
       then
         ((let uu____70789 =
             let uu____70790 = FStar_Tactics_Types.goal_type g  in
             uu____70790.FStar_Syntax_Syntax.pos  in
           let uu____70793 =
             let uu____70799 =
               let uu____70801 = goal_to_string_verbose g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____70801
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____70799)  in
           FStar_Errors.log_issue uu____70789 uu____70793);
          (let uu____70805 =
             let uu____70807 = FStar_ST.op_Bang nwarn  in
             uu____70807 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____70805))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___971_70876 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___971_70876.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___971_70876.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___971_70876.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___971_70876.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___971_70876.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___971_70876.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___971_70876.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___971_70876.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___971_70876.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___971_70876.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___971_70876.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___971_70876.FStar_Tactics_Types.local_state)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___976_70897 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___976_70897.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___976_70897.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___976_70897.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___976_70897.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___976_70897.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___976_70897.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___976_70897.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___976_70897.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___976_70897.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___976_70897.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___976_70897.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___976_70897.FStar_Tactics_Types.local_state)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___981_70918 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___981_70918.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___981_70918.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___981_70918.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___981_70918.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___981_70918.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___981_70918.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___981_70918.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___981_70918.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___981_70918.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___981_70918.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___981_70918.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___981_70918.FStar_Tactics_Types.local_state)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___986_70939 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___986_70939.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___986_70939.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___986_70939.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___986_70939.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___986_70939.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___986_70939.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___986_70939.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___986_70939.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___986_70939.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___986_70939.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___986_70939.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___986_70939.FStar_Tactics_Types.local_state)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____70951  -> add_goals [g]) 
let (new_uvar :
  Prims.string ->
    env ->
      FStar_Reflection_Data.typ ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar) tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____70982 =
          FStar_TypeChecker_Env.new_implicit_var_aux reason
            typ.FStar_Syntax_Syntax.pos env typ
            FStar_Syntax_Syntax.Allow_untyped FStar_Pervasives_Native.None
           in
        match uu____70982 with
        | (u,ctx_uvar,g_u) ->
            let uu____71020 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____71020
              (fun uu____71029  ->
                 let uu____71030 =
                   let uu____71035 =
                     let uu____71036 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____71036  in
                   (u, uu____71035)  in
                 ret uu____71030)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____71057 = FStar_Syntax_Util.un_squash t1  in
    match uu____71057 with
    | FStar_Pervasives_Native.Some t' ->
        let t'1 = FStar_Syntax_Util.unascribe t'  in
        let uu____71069 =
          let uu____71070 = FStar_Syntax_Subst.compress t'1  in
          uu____71070.FStar_Syntax_Syntax.n  in
        (match uu____71069 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____71075 -> false)
    | uu____71077 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____71090 = FStar_Syntax_Util.un_squash t  in
    match uu____71090 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____71101 =
          let uu____71102 = FStar_Syntax_Subst.compress t'  in
          uu____71102.FStar_Syntax_Syntax.n  in
        (match uu____71101 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____71107 -> false)
    | uu____71109 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____71122  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____71134 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____71134 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____71141 = goal_to_string_verbose hd1  in
                    let uu____71143 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____71141 uu____71143);
                   ret hd1)))
  
let (tadmit_t : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____71156 =
      bind get
        (fun ps  ->
           let uu____71162 = cur_goal ()  in
           bind uu____71162
             (fun g  ->
                (let uu____71169 =
                   let uu____71170 = FStar_Tactics_Types.goal_type g  in
                   uu____71170.FStar_Syntax_Syntax.pos  in
                 let uu____71173 =
                   let uu____71179 =
                     let uu____71181 =
                       goal_to_string "" FStar_Pervasives_Native.None ps g
                        in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____71181
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____71179)  in
                 FStar_Errors.log_issue uu____71169 uu____71173);
                solve' g t))
       in
    FStar_All.pipe_left (wrap_err "tadmit_t") uu____71156
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____71204  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___1031_71215 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___1031_71215.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___1031_71215.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___1031_71215.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___1031_71215.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___1031_71215.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___1031_71215.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___1031_71215.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___1031_71215.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___1031_71215.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___1031_71215.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___1031_71215.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (uu___1031_71215.FStar_Tactics_Types.local_state)
           }  in
         let uu____71217 = set ps1  in
         bind uu____71217
           (fun uu____71222  ->
              let uu____71223 = FStar_BigInt.of_int_fs n1  in ret uu____71223))
  
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
              let uu____71261 = env.FStar_TypeChecker_Env.universe_of env phi
                 in
              FStar_Syntax_Util.mk_squash uu____71261 phi  in
            let uu____71262 = new_uvar reason env typ  in
            bind uu____71262
              (fun uu____71277  ->
                 match uu____71277 with
                 | (uu____71284,ctx_uvar) ->
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
             (fun uu____71331  ->
                let uu____71332 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____71332)
             (fun uu____71337  ->
                let e1 =
                  let uu___1049_71339 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1049_71339.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1049_71339.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1049_71339.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1049_71339.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1049_71339.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1049_71339.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1049_71339.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1049_71339.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1049_71339.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1049_71339.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1049_71339.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1049_71339.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1049_71339.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1049_71339.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1049_71339.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1049_71339.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1049_71339.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1049_71339.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1049_71339.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1049_71339.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1049_71339.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1049_71339.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1049_71339.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1049_71339.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1049_71339.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1049_71339.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1049_71339.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1049_71339.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1049_71339.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1049_71339.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1049_71339.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1049_71339.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1049_71339.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1049_71339.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1049_71339.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1049_71339.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1049_71339.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1049_71339.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1049_71339.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1049_71339.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1049_71339.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1049_71339.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___1053_71351  ->
                     match () with
                     | () ->
                         let uu____71360 =
                           FStar_TypeChecker_TcTerm.type_of_tot_term e1 t  in
                         ret uu____71360) ()
                with
                | FStar_Errors.Err (uu____71387,msg) ->
                    let uu____71391 = tts e1 t  in
                    let uu____71393 =
                      let uu____71395 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____71395
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____71391 uu____71393 msg
                | FStar_Errors.Error (uu____71405,msg,uu____71407) ->
                    let uu____71410 = tts e1 t  in
                    let uu____71412 =
                      let uu____71414 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____71414
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____71410 uu____71412 msg))
  
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
             (fun uu____71467  ->
                let uu____71468 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc_ghost(%s)\n" uu____71468)
             (fun uu____71473  ->
                let e1 =
                  let uu___1070_71475 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1070_71475.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1070_71475.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1070_71475.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1070_71475.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1070_71475.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1070_71475.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1070_71475.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1070_71475.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1070_71475.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1070_71475.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1070_71475.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1070_71475.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1070_71475.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1070_71475.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1070_71475.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1070_71475.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1070_71475.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1070_71475.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1070_71475.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1070_71475.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1070_71475.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1070_71475.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1070_71475.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1070_71475.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1070_71475.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1070_71475.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1070_71475.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1070_71475.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1070_71475.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1070_71475.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1070_71475.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1070_71475.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1070_71475.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1070_71475.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1070_71475.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1070_71475.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1070_71475.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1070_71475.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1070_71475.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1070_71475.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1070_71475.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1070_71475.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___1074_71490  ->
                     match () with
                     | () ->
                         let uu____71499 =
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e1 t
                            in
                         (match uu____71499 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____71537,msg) ->
                    let uu____71541 = tts e1 t  in
                    let uu____71543 =
                      let uu____71545 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____71545
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____71541 uu____71543 msg
                | FStar_Errors.Error (uu____71555,msg,uu____71557) ->
                    let uu____71560 = tts e1 t  in
                    let uu____71562 =
                      let uu____71564 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____71564
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____71560 uu____71562 msg))
  
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
             (fun uu____71617  ->
                let uu____71618 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____71618)
             (fun uu____71624  ->
                let e1 =
                  let uu___1095_71626 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1095_71626.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1095_71626.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1095_71626.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1095_71626.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1095_71626.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1095_71626.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1095_71626.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1095_71626.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1095_71626.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1095_71626.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1095_71626.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1095_71626.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1095_71626.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1095_71626.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1095_71626.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1095_71626.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1095_71626.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1095_71626.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1095_71626.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1095_71626.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1095_71626.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1095_71626.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1095_71626.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1095_71626.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1095_71626.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1095_71626.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1095_71626.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1095_71626.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1095_71626.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1095_71626.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1095_71626.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1095_71626.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1095_71626.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1095_71626.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1095_71626.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1095_71626.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1095_71626.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1095_71626.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1095_71626.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1095_71626.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1095_71626.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1095_71626.FStar_TypeChecker_Env.nbe)
                  }  in
                let e2 =
                  let uu___1098_71629 = e1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1098_71629.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1098_71629.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1098_71629.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1098_71629.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1098_71629.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1098_71629.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1098_71629.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1098_71629.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1098_71629.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1098_71629.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1098_71629.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1098_71629.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1098_71629.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1098_71629.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1098_71629.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1098_71629.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1098_71629.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1098_71629.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1098_71629.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1098_71629.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1098_71629.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1098_71629.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1098_71629.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1098_71629.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___1098_71629.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1098_71629.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1098_71629.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1098_71629.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1098_71629.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1098_71629.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1098_71629.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1098_71629.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1098_71629.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1098_71629.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1098_71629.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1098_71629.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1098_71629.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1098_71629.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1098_71629.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1098_71629.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1098_71629.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1098_71629.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___1102_71644  ->
                     match () with
                     | () ->
                         let uu____71653 =
                           FStar_TypeChecker_TcTerm.tc_term e2 t  in
                         (match uu____71653 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____71691,msg) ->
                    let uu____71695 = tts e2 t  in
                    let uu____71697 =
                      let uu____71699 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____71699
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____71695 uu____71697 msg
                | FStar_Errors.Error (uu____71709,msg,uu____71711) ->
                    let uu____71714 = tts e2 t  in
                    let uu____71716 =
                      let uu____71718 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____71718
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____71714 uu____71716 msg))
  
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
  fun uu____71752  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___1127_71771 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___1127_71771.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___1127_71771.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___1127_71771.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___1127_71771.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___1127_71771.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___1127_71771.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___1127_71771.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___1127_71771.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___1127_71771.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___1127_71771.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___1127_71771.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___1127_71771.FStar_Tactics_Types.local_state)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____71796 = get_guard_policy ()  in
      bind uu____71796
        (fun old_pol  ->
           let uu____71802 = set_guard_policy pol  in
           bind uu____71802
             (fun uu____71806  ->
                bind t
                  (fun r  ->
                     let uu____71810 = set_guard_policy old_pol  in
                     bind uu____71810 (fun uu____71814  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____71818 = let uu____71823 = cur_goal ()  in trytac uu____71823  in
  bind uu____71818
    (fun uu___609_71830  ->
       match uu___609_71830 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____71836 = FStar_Options.peek ()  in ret uu____71836)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        mlog
          (fun uu____71861  ->
             let uu____71862 = FStar_TypeChecker_Rel.guard_to_string e g  in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason
               uu____71862)
          (fun uu____71867  ->
             let uu____71868 =
               add_implicits g.FStar_TypeChecker_Env.implicits  in
             bind uu____71868
               (fun uu____71872  ->
                  bind getopts
                    (fun opts  ->
                       let uu____71876 =
                         let uu____71877 =
                           FStar_TypeChecker_Rel.simplify_guard e g  in
                         uu____71877.FStar_TypeChecker_Env.guard_f  in
                       match uu____71876 with
                       | FStar_TypeChecker_Common.Trivial  -> ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____71881 = istrivial e f  in
                           if uu____71881
                           then ret ()
                           else
                             bind get
                               (fun ps  ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop  ->
                                      ((let uu____71894 =
                                          let uu____71900 =
                                            let uu____71902 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g
                                               in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____71902
                                             in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____71900)
                                           in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____71894);
                                       ret ())
                                  | FStar_Tactics_Types.Goal  ->
                                      mlog
                                        (fun uu____71908  ->
                                           let uu____71909 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____71909)
                                        (fun uu____71914  ->
                                           let uu____71915 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____71915
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___1156_71923 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___1156_71923.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___1156_71923.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___1156_71923.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___1156_71923.FStar_Tactics_Types.label)
                                                  }  in
                                                push_goals [goal1]))
                                  | FStar_Tactics_Types.SMT  ->
                                      mlog
                                        (fun uu____71927  ->
                                           let uu____71928 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____71928)
                                        (fun uu____71933  ->
                                           let uu____71934 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____71934
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___1163_71942 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___1163_71942.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___1163_71942.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___1163_71942.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___1163_71942.FStar_Tactics_Types.label)
                                                  }  in
                                                push_smt_goals [goal1]))
                                  | FStar_Tactics_Types.Force  ->
                                      mlog
                                        (fun uu____71946  ->
                                           let uu____71947 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____71947)
                                        (fun uu____71951  ->
                                           try
                                             (fun uu___1170_71956  ->
                                                match () with
                                                | () ->
                                                    let uu____71959 =
                                                      let uu____71961 =
                                                        let uu____71963 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____71963
                                                         in
                                                      Prims.op_Negation
                                                        uu____71961
                                                       in
                                                    if uu____71959
                                                    then
                                                      mlog
                                                        (fun uu____71970  ->
                                                           let uu____71971 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g
                                                              in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____71971)
                                                        (fun uu____71975  ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else ret ()) ()
                                           with
                                           | uu___1169_71980 ->
                                               mlog
                                                 (fun uu____71985  ->
                                                    let uu____71986 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g
                                                       in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____71986)
                                                 (fun uu____71990  ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____72002 =
      let uu____72005 = cur_goal ()  in
      bind uu____72005
        (fun goal  ->
           let uu____72011 =
             let uu____72020 = FStar_Tactics_Types.goal_env goal  in
             __tc_lax uu____72020 t  in
           bind uu____72011
             (fun uu____72031  ->
                match uu____72031 with
                | (uu____72040,typ,uu____72042) -> ret typ))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____72002
  
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
            let uu____72082 = mk_irrelevant_goal reason env phi opts label1
               in
            bind uu____72082 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____72094  ->
    let uu____72097 = cur_goal ()  in
    bind uu____72097
      (fun goal  ->
         let uu____72103 =
           let uu____72105 = FStar_Tactics_Types.goal_env goal  in
           let uu____72106 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____72105 uu____72106  in
         if uu____72103
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____72112 =
              let uu____72114 = FStar_Tactics_Types.goal_env goal  in
              let uu____72115 = FStar_Tactics_Types.goal_type goal  in
              tts uu____72114 uu____72115  in
            fail1 "Not a trivial goal: %s" uu____72112))
  
let divide : 'a 'b . FStar_BigInt.t -> 'a tac -> 'b tac -> ('a * 'b) tac =
  fun n1  ->
    fun l  ->
      fun r  ->
        bind get
          (fun p  ->
             let uu____72166 =
               try
                 (fun uu___1226_72189  ->
                    match () with
                    | () ->
                        let uu____72200 =
                          let uu____72209 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____72209
                            p.FStar_Tactics_Types.goals
                           in
                        ret uu____72200) ()
               with | uu___1225_72220 -> fail "divide: not enough goals"  in
             bind uu____72166
               (fun uu____72257  ->
                  match uu____72257 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___1208_72283 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___1208_72283.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___1208_72283.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___1208_72283.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___1208_72283.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___1208_72283.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___1208_72283.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___1208_72283.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___1208_72283.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___1208_72283.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___1208_72283.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___1208_72283.FStar_Tactics_Types.local_state)
                        }  in
                      let uu____72284 = set lp  in
                      bind uu____72284
                        (fun uu____72292  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___1214_72308 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___1214_72308.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___1214_72308.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___1214_72308.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___1214_72308.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___1214_72308.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___1214_72308.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___1214_72308.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___1214_72308.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___1214_72308.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___1214_72308.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___1214_72308.FStar_Tactics_Types.local_state)
                                       }  in
                                     let uu____72309 = set rp  in
                                     bind uu____72309
                                       (fun uu____72317  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___1220_72333 =
                                                        rp'  in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___1220_72333.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___1220_72333.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___1220_72333.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___1220_72333.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___1220_72333.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___1220_72333.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___1220_72333.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___1220_72333.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___1220_72333.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___1220_72333.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___1220_72333.FStar_Tactics_Types.local_state)
                                                      }  in
                                                    let uu____72334 = set p'
                                                       in
                                                    bind uu____72334
                                                      (fun uu____72342  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____72348 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____72370 = divide FStar_BigInt.one f idtac  in
    bind uu____72370
      (fun uu____72383  -> match uu____72383 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____72421::uu____72422 ->
             let uu____72425 =
               let uu____72434 = map tau  in
               divide FStar_BigInt.one tau uu____72434  in
             bind uu____72425
               (fun uu____72452  ->
                  match uu____72452 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____72494 =
        bind t1
          (fun uu____72499  ->
             let uu____72500 = map t2  in
             bind uu____72500 (fun uu____72508  -> ret ()))
         in
      focus uu____72494
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____72518  ->
    let uu____72521 =
      let uu____72524 = cur_goal ()  in
      bind uu____72524
        (fun goal  ->
           let uu____72533 =
             let uu____72540 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____72540  in
           match uu____72533 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____72549 =
                 let uu____72551 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____72551  in
               if uu____72549
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____72560 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____72560 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____72574 = new_uvar "intro" env' typ'  in
                  bind uu____72574
                    (fun uu____72591  ->
                       match uu____72591 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c))
                              in
                           let uu____72615 = set_solution goal sol  in
                           bind uu____72615
                             (fun uu____72621  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                    goal.FStar_Tactics_Types.label
                                   in
                                let uu____72623 =
                                  let uu____72626 = bnorm_goal g  in
                                  replace_cur uu____72626  in
                                bind uu____72623 (fun uu____72628  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____72633 =
                 let uu____72635 = FStar_Tactics_Types.goal_env goal  in
                 let uu____72636 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____72635 uu____72636  in
               fail1 "goal is not an arrow (%s)" uu____72633)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____72521
  
let (intro_rec :
  unit -> (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder) tac) =
  fun uu____72654  ->
    let uu____72661 = cur_goal ()  in
    bind uu____72661
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____72680 =
            let uu____72687 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____72687  in
          match uu____72680 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____72700 =
                let uu____72702 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____72702  in
              if uu____72700
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____72719 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____72719
                    in
                 let bs =
                   let uu____72730 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____72730; b]  in
                 let env' =
                   let uu____72756 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____72756 bs  in
                 let uu____72757 =
                   let uu____72764 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____72764  in
                 bind uu____72757
                   (fun uu____72784  ->
                      match uu____72784 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____72798 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____72801 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____72798
                              FStar_Parser_Const.effect_Tot_lid uu____72801
                              [] FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____72819 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____72819 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____72841 =
                                   let uu____72842 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____72842.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____72841
                                  in
                               let uu____72858 = set_solution goal tm  in
                               bind uu____72858
                                 (fun uu____72867  ->
                                    let uu____72868 =
                                      let uu____72871 =
                                        bnorm_goal
                                          (let uu___1291_72874 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___1291_72874.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___1291_72874.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___1291_72874.FStar_Tactics_Types.is_guard);
                                             FStar_Tactics_Types.label =
                                               (uu___1291_72874.FStar_Tactics_Types.label)
                                           })
                                         in
                                      replace_cur uu____72871  in
                                    bind uu____72868
                                      (fun uu____72881  ->
                                         let uu____72882 =
                                           let uu____72887 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____72887, b)  in
                                         ret uu____72882)))))
          | FStar_Pervasives_Native.None  ->
              let uu____72896 =
                let uu____72898 = FStar_Tactics_Types.goal_env goal  in
                let uu____72899 = FStar_Tactics_Types.goal_type goal  in
                tts uu____72898 uu____72899  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____72896))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____72919 = cur_goal ()  in
    bind uu____72919
      (fun goal  ->
         mlog
           (fun uu____72926  ->
              let uu____72927 =
                let uu____72929 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____72929  in
              FStar_Util.print1 "norm: witness = %s\n" uu____72927)
           (fun uu____72935  ->
              let steps =
                let uu____72939 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____72939
                 in
              let t =
                let uu____72943 = FStar_Tactics_Types.goal_env goal  in
                let uu____72944 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____72943 uu____72944  in
              let uu____72945 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____72945))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____72970 =
          bind get
            (fun ps  ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
                 | g::uu____72978 -> g.FStar_Tactics_Types.opts
                 | uu____72981 -> FStar_Options.peek ()  in
               mlog
                 (fun uu____72986  ->
                    let uu____72987 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____72987)
                 (fun uu____72992  ->
                    let uu____72993 = __tc_lax e t  in
                    bind uu____72993
                      (fun uu____73014  ->
                         match uu____73014 with
                         | (t1,uu____73024,uu____73025) ->
                             let steps =
                               let uu____73029 =
                                 FStar_TypeChecker_Normalize.tr_norm_steps s
                                  in
                               FStar_List.append
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu____73029
                                in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1
                                in
                             mlog
                               (fun uu____73035  ->
                                  let uu____73036 =
                                    FStar_Syntax_Print.term_to_string t2  in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____73036)
                               (fun uu____73040  -> ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____72970
  
let (refine_intro : unit -> unit tac) =
  fun uu____73053  ->
    let uu____73056 =
      let uu____73059 = cur_goal ()  in
      bind uu____73059
        (fun g  ->
           let uu____73066 =
             let uu____73077 = FStar_Tactics_Types.goal_env g  in
             let uu____73078 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____73077
               uu____73078
              in
           match uu____73066 with
           | (uu____73081,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____73107 =
                 let uu____73112 =
                   let uu____73117 =
                     let uu____73118 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____73118]  in
                   FStar_Syntax_Subst.open_term uu____73117 phi  in
                 match uu____73112 with
                 | (bvs,phi1) ->
                     let uu____73143 =
                       let uu____73144 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____73144  in
                     (uu____73143, phi1)
                  in
               (match uu____73107 with
                | (bv1,phi1) ->
                    let uu____73163 =
                      let uu____73166 = FStar_Tactics_Types.goal_env g  in
                      let uu____73167 =
                        let uu____73168 =
                          let uu____73171 =
                            let uu____73172 =
                              let uu____73179 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____73179)  in
                            FStar_Syntax_Syntax.NT uu____73172  in
                          [uu____73171]  in
                        FStar_Syntax_Subst.subst uu____73168 phi1  in
                      mk_irrelevant_goal "refine_intro refinement"
                        uu____73166 uu____73167 g.FStar_Tactics_Types.opts
                        g.FStar_Tactics_Types.label
                       in
                    bind uu____73163
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____73188  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____73056
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____73211 = cur_goal ()  in
      bind uu____73211
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____73220 = FStar_Tactics_Types.goal_env goal  in
               let uu____73221 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____73220 uu____73221
             else FStar_Tactics_Types.goal_env goal  in
           let uu____73224 = __tc env t  in
           bind uu____73224
             (fun uu____73243  ->
                match uu____73243 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____73258  ->
                         let uu____73259 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____73261 =
                           let uu____73263 =
                             FStar_Tactics_Types.goal_env goal  in
                           FStar_TypeChecker_Rel.guard_to_string uu____73263
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____73259 uu____73261)
                      (fun uu____73267  ->
                         let uu____73268 =
                           let uu____73271 =
                             FStar_Tactics_Types.goal_env goal  in
                           proc_guard "__exact typing" uu____73271 guard  in
                         bind uu____73268
                           (fun uu____73274  ->
                              mlog
                                (fun uu____73278  ->
                                   let uu____73279 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____73281 =
                                     let uu____73283 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____73283
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____73279 uu____73281)
                                (fun uu____73287  ->
                                   let uu____73288 =
                                     let uu____73292 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____73293 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____73292 typ uu____73293  in
                                   bind uu____73288
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____73303 =
                                             let uu____73305 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____73305 t1  in
                                           let uu____73306 =
                                             let uu____73308 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____73308 typ  in
                                           let uu____73309 =
                                             let uu____73311 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____73312 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____73311 uu____73312  in
                                           let uu____73313 =
                                             let uu____73315 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____73316 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____73315 uu____73316  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____73303 uu____73306
                                             uu____73309 uu____73313)))))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun try_refine  ->
    fun set_expected_typ1  ->
      fun tm  ->
        let uu____73342 =
          mlog
            (fun uu____73347  ->
               let uu____73348 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____73348)
            (fun uu____73353  ->
               let uu____73354 =
                 let uu____73361 = __exact_now set_expected_typ1 tm  in
                 catch uu____73361  in
               bind uu____73354
                 (fun uu___611_73370  ->
                    match uu___611_73370 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        traise e
                    | FStar_Util.Inl e ->
                        mlog
                          (fun uu____73381  ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____73385  ->
                             let uu____73386 =
                               let uu____73393 =
                                 let uu____73396 =
                                   norm [FStar_Syntax_Embeddings.Delta]  in
                                 bind uu____73396
                                   (fun uu____73401  ->
                                      let uu____73402 = refine_intro ()  in
                                      bind uu____73402
                                        (fun uu____73406  ->
                                           __exact_now set_expected_typ1 tm))
                                  in
                               catch uu____73393  in
                             bind uu____73386
                               (fun uu___610_73413  ->
                                  match uu___610_73413 with
                                  | FStar_Util.Inr r ->
                                      mlog
                                        (fun uu____73422  ->
                                           FStar_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu____73425  -> ret ())
                                  | FStar_Util.Inl uu____73426 ->
                                      mlog
                                        (fun uu____73428  ->
                                           FStar_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu____73431  -> traise e)))))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____73342
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____73483 = f x  in
          bind uu____73483
            (fun y  ->
               let uu____73491 = mapM f xs  in
               bind uu____73491 (fun ys  -> ret (y :: ys)))
  
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
          let uu____73563 = do_unify e ty1 ty2  in
          bind uu____73563
            (fun uu___612_73577  ->
               if uu___612_73577
               then ret acc
               else
                 (let uu____73597 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____73597 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____73618 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____73620 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____73618
                        uu____73620
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____73637 =
                        let uu____73639 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____73639  in
                      if uu____73637
                      then fail "Codomain is effectful"
                      else
                        (let uu____73663 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____73663
                           (fun uu____73690  ->
                              match uu____73690 with
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
      let uu____73780 =
        mlog
          (fun uu____73785  ->
             let uu____73786 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_apply: tm = %s\n" uu____73786)
          (fun uu____73791  ->
             let uu____73792 = cur_goal ()  in
             bind uu____73792
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____73800 = __tc e tm  in
                  bind uu____73800
                    (fun uu____73821  ->
                       match uu____73821 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____73834 =
                             let uu____73845 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____73845  in
                           bind uu____73834
                             (fun uvs  ->
                                let fix_qual q =
                                  match q with
                                  | FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Meta uu____73883)
                                      ->
                                      FStar_Pervasives_Native.Some
                                        (FStar_Syntax_Syntax.Implicit false)
                                  | uu____73887 -> q  in
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____73910  ->
                                       fun w  ->
                                         match uu____73910 with
                                         | (uvt,q,uu____73928) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, (fix_qual q))]) uvs tm1
                                   in
                                let uvset =
                                  let uu____73960 =
                                    FStar_Syntax_Free.new_uv_set ()  in
                                  FStar_List.fold_right
                                    (fun uu____73977  ->
                                       fun s  ->
                                         match uu____73977 with
                                         | (uu____73989,uu____73990,uv) ->
                                             let uu____73992 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                in
                                             FStar_Util.set_union s
                                               uu____73992) uvs uu____73960
                                   in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset  in
                                let uu____74002 = solve' goal w  in
                                bind uu____74002
                                  (fun uu____74007  ->
                                     let uu____74008 =
                                       mapM
                                         (fun uu____74025  ->
                                            match uu____74025 with
                                            | (uvt,q,uv) ->
                                                let uu____74037 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                   in
                                                (match uu____74037 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____74042 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____74043 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv)
                                                        in
                                                     if uu____74043
                                                     then ret ()
                                                     else
                                                       (let uu____74050 =
                                                          let uu____74053 =
                                                            bnorm_goal
                                                              (let uu___1452_74056
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___1452_74056.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___1452_74056.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false;
                                                                 FStar_Tactics_Types.label
                                                                   =
                                                                   (uu___1452_74056.FStar_Tactics_Types.label)
                                                               })
                                                             in
                                                          [uu____74053]  in
                                                        add_goals uu____74050)))
                                         uvs
                                        in
                                     bind uu____74008
                                       (fun uu____74061  ->
                                          proc_guard "apply guard" e guard))))))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____73780
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____74089 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____74089
    then
      let uu____74098 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____74113 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____74166 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____74098 with
      | (pre,post) ->
          let post1 =
            let uu____74199 =
              let uu____74210 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____74210]  in
            FStar_Syntax_Util.mk_app post uu____74199  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____74241 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____74241
       then
         let uu____74250 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____74250
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
            let uu____74329 = f x e  in
            bind uu____74329 (fun e'  -> fold_left f e' xs1)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____74344 =
      let uu____74347 =
        bind get
          (fun ps  ->
             mlog
               (fun uu____74354  ->
                  let uu____74355 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____74355)
               (fun uu____74361  ->
                  let is_unit_t t =
                    let uu____74369 =
                      let uu____74370 = FStar_Syntax_Subst.compress t  in
                      uu____74370.FStar_Syntax_Syntax.n  in
                    match uu____74369 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____74376 -> false  in
                  let uu____74378 = cur_goal ()  in
                  bind uu____74378
                    (fun goal  ->
                       let uu____74384 =
                         let uu____74393 = FStar_Tactics_Types.goal_env goal
                            in
                         __tc uu____74393 tm  in
                       bind uu____74384
                         (fun uu____74408  ->
                            match uu____74408 with
                            | (tm1,t,guard) ->
                                let uu____74420 =
                                  FStar_Syntax_Util.arrow_formals_comp t  in
                                (match uu____74420 with
                                 | (bs,comp) ->
                                     let uu____74453 = lemma_or_sq comp  in
                                     (match uu____74453 with
                                      | FStar_Pervasives_Native.None  ->
                                          fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre,post) ->
                                          let uu____74473 =
                                            fold_left
                                              (fun uu____74535  ->
                                                 fun uu____74536  ->
                                                   match (uu____74535,
                                                           uu____74536)
                                                   with
                                                   | ((b,aq),(uvs,imps,subst1))
                                                       ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst1
                                                           b.FStar_Syntax_Syntax.sort
                                                          in
                                                       let uu____74687 =
                                                         is_unit_t b_t  in
                                                       if uu____74687
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
                                                         (let uu____74810 =
                                                            let uu____74817 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            new_uvar
                                                              "apply_lemma"
                                                              uu____74817 b_t
                                                             in
                                                          bind uu____74810
                                                            (fun uu____74848 
                                                               ->
                                                               match uu____74848
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
                                          bind uu____74473
                                            (fun uu____75034  ->
                                               match uu____75034 with
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
                                                   let uu____75122 =
                                                     let uu____75126 =
                                                       FStar_Tactics_Types.goal_env
                                                         goal
                                                        in
                                                     let uu____75127 =
                                                       FStar_Syntax_Util.mk_squash
                                                         FStar_Syntax_Syntax.U_zero
                                                         post1
                                                        in
                                                     let uu____75128 =
                                                       FStar_Tactics_Types.goal_type
                                                         goal
                                                        in
                                                     do_unify uu____75126
                                                       uu____75127
                                                       uu____75128
                                                      in
                                                   bind uu____75122
                                                     (fun b  ->
                                                        if
                                                          Prims.op_Negation b
                                                        then
                                                          let uu____75139 =
                                                            let uu____75141 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            tts uu____75141
                                                              tm1
                                                             in
                                                          let uu____75142 =
                                                            let uu____75144 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            let uu____75145 =
                                                              FStar_Syntax_Util.mk_squash
                                                                FStar_Syntax_Syntax.U_zero
                                                                post1
                                                               in
                                                            tts uu____75144
                                                              uu____75145
                                                             in
                                                          let uu____75146 =
                                                            let uu____75148 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            let uu____75149 =
                                                              FStar_Tactics_Types.goal_type
                                                                goal
                                                               in
                                                            tts uu____75148
                                                              uu____75149
                                                             in
                                                          fail3
                                                            "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                            uu____75139
                                                            uu____75142
                                                            uu____75146
                                                        else
                                                          (let uu____75153 =
                                                             solve' goal
                                                               FStar_Syntax_Util.exp_unit
                                                              in
                                                           bind uu____75153
                                                             (fun uu____75161
                                                                 ->
                                                                let is_free_uvar
                                                                  uv t1 =
                                                                  let free_uvars
                                                                    =
                                                                    let uu____75187
                                                                    =
                                                                    let uu____75190
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____75190
                                                                     in
                                                                    FStar_List.map
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____75187
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
                                                                    let uu____75226
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____75226)
                                                                    goals
                                                                   in
                                                                let checkone
                                                                  t1 goals =
                                                                  let uu____75243
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                  match uu____75243
                                                                  with
                                                                  | (hd1,uu____75262)
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____75289)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____75306
                                                                    -> false)
                                                                   in
                                                                let uu____75308
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
                                                                    let uu____75351
                                                                    = imp  in
                                                                    match uu____75351
                                                                    with
                                                                    | 
                                                                    (term,ctx_uvar)
                                                                    ->
                                                                    let uu____75362
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____75362
                                                                    with
                                                                    | 
                                                                    (hd1,uu____75384)
                                                                    ->
                                                                    let uu____75409
                                                                    =
                                                                    let uu____75410
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____75410.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____75409
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____75418)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___1562_75438
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___1562_75438.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___1562_75438.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___1562_75438.FStar_Tactics_Types.is_guard);
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___1562_75438.FStar_Tactics_Types.label)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____75441
                                                                    ->
                                                                    mlog
                                                                    (fun
                                                                    uu____75447
                                                                     ->
                                                                    let uu____75448
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                                                     in
                                                                    let uu____75450
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____75448
                                                                    uu____75450)
                                                                    (fun
                                                                    uu____75457
                                                                     ->
                                                                    let env =
                                                                    let uu___1567_75459
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___1567_75459.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1567_75459.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1567_75459.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___1567_75459.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1567_75459.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1567_75459.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1567_75459.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1567_75459.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___1567_75459.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___1567_75459.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___1567_75459.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1567_75459.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1567_75459.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1567_75459.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1567_75459.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1567_75459.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1567_75459.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1567_75459.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___1567_75459.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___1567_75459.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___1567_75459.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1567_75459.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1567_75459.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1567_75459.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1567_75459.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1567_75459.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1567_75459.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1567_75459.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1567_75459.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1567_75459.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1567_75459.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1567_75459.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1567_75459.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1567_75459.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___1567_75459.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1567_75459.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1567_75459.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___1567_75459.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1567_75459.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1567_75459.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1567_75459.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1567_75459.FStar_TypeChecker_Env.nbe)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let uu____75462
                                                                    =
                                                                    let uu____75465
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____75469
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
                                                                    let uu____75471
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____75469
                                                                    uu____75471
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____75477
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    uu____75465
                                                                    uu____75477
                                                                    g_typ  in
                                                                    bind
                                                                    uu____75462
                                                                    (fun
                                                                    uu____75481
                                                                     ->
                                                                    ret []))))))
                                                                   in
                                                                bind
                                                                  uu____75308
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
                                                                    let uu____75545
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____75545
                                                                    then
                                                                    let uu____75550
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____75550
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
                                                                    let uu____75565
                                                                    =
                                                                    let uu____75567
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____75567
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____75565)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____75568
                                                                    =
                                                                    let uu____75571
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____75571
                                                                    guard  in
                                                                    bind
                                                                    uu____75568
                                                                    (fun
                                                                    uu____75575
                                                                     ->
                                                                    let uu____75576
                                                                    =
                                                                    let uu____75579
                                                                    =
                                                                    let uu____75581
                                                                    =
                                                                    let uu____75583
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____75584
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____75583
                                                                    uu____75584
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____75581
                                                                     in
                                                                    if
                                                                    uu____75579
                                                                    then
                                                                    let uu____75588
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____75588
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    goal.FStar_Tactics_Types.label
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____75576
                                                                    (fun
                                                                    uu____75593
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2)))))))))))))
         in
      focus uu____74347  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____74344
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____75617 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____75617 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____75627::(e1,uu____75629)::(e2,uu____75631)::[])) when
        (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) ||
          (FStar_Ident.lid_equals l FStar_Parser_Const.c_eq2_lid)
        -> FStar_Pervasives_Native.Some (e1, e2)
    | uu____75692 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____75717 = destruct_eq' typ  in
    match uu____75717 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____75747 = FStar_Syntax_Util.un_squash typ  in
        (match uu____75747 with
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
        let uu____75816 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____75816 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', bv', [])
            else
              (let uu____75874 = aux e'  in
               FStar_Util.map_opt uu____75874
                 (fun uu____75905  ->
                    match uu____75905 with
                    | (e'',bv,bvs) -> (e'', bv, (bv' :: bvs))))
         in
      let uu____75931 = aux e  in
      FStar_Util.map_opt uu____75931
        (fun uu____75962  ->
           match uu____75962 with
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
          let uu____76036 =
            let uu____76047 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____76047  in
          FStar_Util.map_opt uu____76036
            (fun uu____76065  ->
               match uu____76065 with
               | (e0,b11,bvs) ->
                   let s1 bv =
                     let uu___1640_76087 = bv  in
                     let uu____76088 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___1640_76087.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___1640_76087.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____76088
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___1644_76096 =
                       g.FStar_Tactics_Types.goal_ctx_uvar  in
                     let uu____76097 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____76106 =
                       let uu____76109 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____76109  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___1644_76096.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____76097;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____76106;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___1644_76096.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___1644_76096.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___1644_76096.FStar_Syntax_Syntax.ctx_uvar_range);
                       FStar_Syntax_Syntax.ctx_uvar_meta =
                         (uu___1644_76096.FStar_Syntax_Syntax.ctx_uvar_meta)
                     }  in
                   let uu___1647_76110 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1647_76110.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___1647_76110.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___1647_76110.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1647_76110.FStar_Tactics_Types.label)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____76121 =
      let uu____76124 = cur_goal ()  in
      bind uu____76124
        (fun goal  ->
           let uu____76132 = h  in
           match uu____76132 with
           | (bv,uu____76136) ->
               mlog
                 (fun uu____76144  ->
                    let uu____76145 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____76147 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____76145
                      uu____76147)
                 (fun uu____76152  ->
                    let uu____76153 =
                      let uu____76164 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____76164  in
                    match uu____76153 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                        let uu____76191 =
                          destruct_eq bv1.FStar_Syntax_Syntax.sort  in
                        (match uu____76191 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____76206 =
                               let uu____76207 =
                                 FStar_Syntax_Subst.compress x  in
                               uu____76207.FStar_Syntax_Syntax.n  in
                             (match uu____76206 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv2 =
                                    let uu___1670_76224 = bv2  in
                                    let uu____76225 =
                                      FStar_Syntax_Subst.subst s
                                        bv2.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1670_76224.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1670_76224.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____76225
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv1 :: bvs1)  in
                                  let new_goal =
                                    let uu___1674_76233 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____76234 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____76243 =
                                      let uu____76246 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____76246
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___1674_76233.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____76234;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____76243;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___1674_76233.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___1674_76233.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___1674_76233.FStar_Syntax_Syntax.ctx_uvar_range);
                                      FStar_Syntax_Syntax.ctx_uvar_meta =
                                        (uu___1674_76233.FStar_Syntax_Syntax.ctx_uvar_meta)
                                    }  in
                                  replace_cur
                                    (let uu___1677_76249 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___1677_76249.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___1677_76249.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___1677_76249.FStar_Tactics_Types.is_guard);
                                       FStar_Tactics_Types.label =
                                         (uu___1677_76249.FStar_Tactics_Types.label)
                                     })
                              | uu____76250 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____76252 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____76121
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____76282 =
        let uu____76285 = cur_goal ()  in
        bind uu____76285
          (fun goal  ->
             let uu____76296 = b  in
             match uu____76296 with
             | (bv,uu____76300) ->
                 let bv' =
                   let uu____76306 =
                     let uu___1688_76307 = bv  in
                     let uu____76308 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____76308;
                       FStar_Syntax_Syntax.index =
                         (uu___1688_76307.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___1688_76307.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____76306  in
                 let s1 =
                   let uu____76313 =
                     let uu____76314 =
                       let uu____76321 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____76321)  in
                     FStar_Syntax_Syntax.NT uu____76314  in
                   [uu____76313]  in
                 let uu____76326 = subst_goal bv bv' s1 goal  in
                 (match uu____76326 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____76282
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____76348 =
      let uu____76351 = cur_goal ()  in
      bind uu____76351
        (fun goal  ->
           let uu____76360 = b  in
           match uu____76360 with
           | (bv,uu____76364) ->
               let uu____76369 =
                 let uu____76380 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____76380  in
               (match uu____76369 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                    let uu____76407 = FStar_Syntax_Util.type_u ()  in
                    (match uu____76407 with
                     | (ty,u) ->
                         let uu____76416 = new_uvar "binder_retype" e0 ty  in
                         bind uu____76416
                           (fun uu____76435  ->
                              match uu____76435 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___1712_76445 = bv1  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1712_76445.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1712_76445.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____76449 =
                                      let uu____76450 =
                                        let uu____76457 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv1, uu____76457)  in
                                      FStar_Syntax_Syntax.NT uu____76450  in
                                    [uu____76449]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___1717_76469 = b1  in
                                         let uu____76470 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___1717_76469.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___1717_76469.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____76470
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____76477  ->
                                       let new_goal =
                                         let uu____76479 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____76480 =
                                           let uu____76481 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____76481
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____76479 uu____76480
                                          in
                                       let uu____76482 = add_goals [new_goal]
                                          in
                                       bind uu____76482
                                         (fun uu____76487  ->
                                            let uu____76488 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv1.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____76488
                                              goal.FStar_Tactics_Types.opts
                                              goal.FStar_Tactics_Types.label))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____76348
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____76514 =
        let uu____76517 = cur_goal ()  in
        bind uu____76517
          (fun goal  ->
             let uu____76526 = b  in
             match uu____76526 with
             | (bv,uu____76530) ->
                 let uu____76535 =
                   let uu____76546 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____76546  in
                 (match uu____76535 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                      let steps =
                        let uu____76576 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____76576
                         in
                      let sort' =
                        normalize steps e0 bv1.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___1738_76581 = bv1  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___1738_76581.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___1738_76581.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____76583 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____76583))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____76514
  
let (revert : unit -> unit tac) =
  fun uu____76596  ->
    let uu____76599 = cur_goal ()  in
    bind uu____76599
      (fun goal  ->
         let uu____76605 =
           let uu____76612 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____76612  in
         match uu____76605 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____76629 =
                 let uu____76632 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____76632  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____76629
                in
             let uu____76647 = new_uvar "revert" env' typ'  in
             bind uu____76647
               (fun uu____76663  ->
                  match uu____76663 with
                  | (r,u_r) ->
                      let uu____76672 =
                        let uu____76675 =
                          let uu____76676 =
                            let uu____76677 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____76677.FStar_Syntax_Syntax.pos  in
                          let uu____76680 =
                            let uu____76685 =
                              let uu____76686 =
                                let uu____76695 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____76695  in
                              [uu____76686]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____76685  in
                          uu____76680 FStar_Pervasives_Native.None
                            uu____76676
                           in
                        set_solution goal uu____76675  in
                      bind uu____76672
                        (fun uu____76716  ->
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
      let uu____76730 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____76730
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____76746 = cur_goal ()  in
    bind uu____76746
      (fun goal  ->
         mlog
           (fun uu____76754  ->
              let uu____76755 = FStar_Syntax_Print.binder_to_string b  in
              let uu____76757 =
                let uu____76759 =
                  let uu____76761 =
                    let uu____76770 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____76770  in
                  FStar_All.pipe_right uu____76761 FStar_List.length  in
                FStar_All.pipe_right uu____76759 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____76755 uu____76757)
           (fun uu____76791  ->
              let uu____76792 =
                let uu____76803 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____76803  in
              match uu____76792 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bv1,bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____76848 =
                          free_in bv1 bv'.FStar_Syntax_Syntax.sort  in
                        if uu____76848
                        then
                          let uu____76853 =
                            let uu____76855 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____76855
                             in
                          fail uu____76853
                        else check1 bvs2
                     in
                  let uu____76860 =
                    let uu____76862 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv1 uu____76862  in
                  if uu____76860
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____76869 = check1 bvs  in
                     bind uu____76869
                       (fun uu____76875  ->
                          let env' = push_bvs e' bvs  in
                          let uu____76877 =
                            let uu____76884 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____76884  in
                          bind uu____76877
                            (fun uu____76894  ->
                               match uu____76894 with
                               | (ut,uvar_ut) ->
                                   let uu____76903 = set_solution goal ut  in
                                   bind uu____76903
                                     (fun uu____76908  ->
                                        let uu____76909 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                            goal.FStar_Tactics_Types.label
                                           in
                                        replace_cur uu____76909))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____76917  ->
    let uu____76920 = cur_goal ()  in
    bind uu____76920
      (fun goal  ->
         let uu____76926 =
           let uu____76933 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____76933  in
         match uu____76926 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____76942) ->
             let uu____76947 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____76947)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____76960 = cur_goal ()  in
    bind uu____76960
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____76970 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____76970  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____76973  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____76986 = cur_goal ()  in
    bind uu____76986
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____76996 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____76996  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____76999  -> add_goals [g']))
  
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
            let uu____77040 = FStar_Syntax_Subst.compress t  in
            uu____77040.FStar_Syntax_Syntax.n  in
          let uu____77043 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___1922_77050 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___1922_77050.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___1922_77050.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____77043
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____77067 =
                   let uu____77068 = FStar_Syntax_Subst.compress t1  in
                   uu____77068.FStar_Syntax_Syntax.n  in
                 match uu____77067 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____77099 = ff hd1  in
                     bind uu____77099
                       (fun hd2  ->
                          let fa uu____77125 =
                            match uu____77125 with
                            | (a,q) ->
                                let uu____77146 = ff a  in
                                bind uu____77146 (fun a1  -> ret (a1, q))
                             in
                          let uu____77165 = mapM fa args  in
                          bind uu____77165
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____77247 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____77247 with
                      | (bs1,t') ->
                          let uu____77256 =
                            let uu____77259 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____77259 t'  in
                          bind uu____77256
                            (fun t''  ->
                               let uu____77263 =
                                 let uu____77264 =
                                   let uu____77283 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____77292 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____77283, uu____77292, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____77264  in
                               ret uu____77263))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____77367 = ff hd1  in
                     bind uu____77367
                       (fun hd2  ->
                          let ffb br =
                            let uu____77382 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____77382 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____77414 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____77414  in
                                let uu____77415 = ff1 e  in
                                bind uu____77415
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____77430 = mapM ffb brs  in
                          bind uu____77430
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____77474;
                          FStar_Syntax_Syntax.lbtyp = uu____77475;
                          FStar_Syntax_Syntax.lbeff = uu____77476;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____77478;
                          FStar_Syntax_Syntax.lbpos = uu____77479;_}::[]),e)
                     ->
                     let lb =
                       let uu____77507 =
                         let uu____77508 = FStar_Syntax_Subst.compress t1  in
                         uu____77508.FStar_Syntax_Syntax.n  in
                       match uu____77507 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____77512) -> lb
                       | uu____77528 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____77538 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____77538
                         (fun def1  ->
                            ret
                              (let uu___1875_77544 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1875_77544.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1875_77544.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1875_77544.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1875_77544.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1875_77544.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1875_77544.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____77545 = fflb lb  in
                     bind uu____77545
                       (fun lb1  ->
                          let uu____77555 =
                            let uu____77560 =
                              let uu____77561 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____77561]  in
                            FStar_Syntax_Subst.open_term uu____77560 e  in
                          match uu____77555 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____77591 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____77591  in
                              let uu____77592 = ff1 e1  in
                              bind uu____77592
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____77639 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____77639
                         (fun def  ->
                            ret
                              (let uu___1893_77645 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1893_77645.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1893_77645.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1893_77645.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1893_77645.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1893_77645.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1893_77645.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____77646 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____77646 with
                      | (lbs1,e1) ->
                          let uu____77661 = mapM fflb lbs1  in
                          bind uu____77661
                            (fun lbs2  ->
                               let uu____77673 = ff e1  in
                               bind uu____77673
                                 (fun e2  ->
                                    let uu____77681 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____77681 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____77752 = ff t2  in
                     bind uu____77752
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____77783 = ff t2  in
                     bind uu____77783
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____77790 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___1917_77797 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___1917_77797.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___1917_77797.FStar_Syntax_Syntax.vars)
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
              let uu____77844 =
                FStar_TypeChecker_TcTerm.tc_term
                  (let uu___1930_77853 = env  in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___1930_77853.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___1930_77853.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___1930_77853.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___1930_77853.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_sig =
                       (uu___1930_77853.FStar_TypeChecker_Env.gamma_sig);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___1930_77853.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___1930_77853.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___1930_77853.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___1930_77853.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.attrtab =
                       (uu___1930_77853.FStar_TypeChecker_Env.attrtab);
                     FStar_TypeChecker_Env.is_pattern =
                       (uu___1930_77853.FStar_TypeChecker_Env.is_pattern);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___1930_77853.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___1930_77853.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___1930_77853.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___1930_77853.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___1930_77853.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___1930_77853.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___1930_77853.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___1930_77853.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___1930_77853.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax = true;
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___1930_77853.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.phase1 =
                       (uu___1930_77853.FStar_TypeChecker_Env.phase1);
                     FStar_TypeChecker_Env.failhard =
                       (uu___1930_77853.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___1930_77853.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.uvar_subtyping =
                       (uu___1930_77853.FStar_TypeChecker_Env.uvar_subtyping);
                     FStar_TypeChecker_Env.tc_term =
                       (uu___1930_77853.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.type_of =
                       (uu___1930_77853.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___1930_77853.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.check_type_of =
                       (uu___1930_77853.FStar_TypeChecker_Env.check_type_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___1930_77853.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (uu___1930_77853.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (uu___1930_77853.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.fv_delta_depths =
                       (uu___1930_77853.FStar_TypeChecker_Env.fv_delta_depths);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___1930_77853.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (uu___1930_77853.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.splice =
                       (uu___1930_77853.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.postprocess =
                       (uu___1930_77853.FStar_TypeChecker_Env.postprocess);
                     FStar_TypeChecker_Env.is_native_tactic =
                       (uu___1930_77853.FStar_TypeChecker_Env.is_native_tactic);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___1930_77853.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (uu___1930_77853.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (uu___1930_77853.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.nbe =
                       (uu___1930_77853.FStar_TypeChecker_Env.nbe)
                   }) t
                 in
              match uu____77844 with
              | (t1,lcomp,g) ->
                  let uu____77860 =
                    (let uu____77864 =
                       FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                     Prims.op_Negation uu____77864) ||
                      (let uu____77867 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____77867)
                     in
                  if uu____77860
                  then ret t1
                  else
                    (let rewrite_eq =
                       let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                       let uu____77878 = new_uvar "pointwise_rec" env typ  in
                       bind uu____77878
                         (fun uu____77895  ->
                            match uu____77895 with
                            | (ut,uvar_ut) ->
                                (log ps
                                   (fun uu____77908  ->
                                      let uu____77909 =
                                        FStar_Syntax_Print.term_to_string t1
                                         in
                                      let uu____77911 =
                                        FStar_Syntax_Print.term_to_string ut
                                         in
                                      FStar_Util.print2
                                        "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                        uu____77909 uu____77911);
                                 (let uu____77914 =
                                    let uu____77917 =
                                      let uu____77918 =
                                        FStar_TypeChecker_TcTerm.universe_of
                                          env typ
                                         in
                                      FStar_Syntax_Util.mk_eq2 uu____77918
                                        typ t1 ut
                                       in
                                    add_irrelevant_goal
                                      "pointwise_rec equation" env
                                      uu____77917 opts label1
                                     in
                                  bind uu____77914
                                    (fun uu____77922  ->
                                       let uu____77923 =
                                         bind tau
                                           (fun uu____77929  ->
                                              let ut1 =
                                                FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                  env ut
                                                 in
                                              log ps
                                                (fun uu____77935  ->
                                                   let uu____77936 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1
                                                      in
                                                   let uu____77938 =
                                                     FStar_Syntax_Print.term_to_string
                                                       ut1
                                                      in
                                                   FStar_Util.print2
                                                     "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                     uu____77936 uu____77938);
                                              ret ut1)
                                          in
                                       focus uu____77923))))
                        in
                     let uu____77941 = catch rewrite_eq  in
                     bind uu____77941
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
          let uu____78159 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____78159
            (fun t1  ->
               let uu____78167 =
                 f env
                   (let uu___2007_78176 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___2007_78176.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___2007_78176.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____78167
                 (fun uu____78192  ->
                    match uu____78192 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____78215 =
                               let uu____78216 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____78216.FStar_Syntax_Syntax.n  in
                             match uu____78215 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____78253 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____78253
                                   (fun uu____78278  ->
                                      match uu____78278 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____78294 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____78294
                                            (fun uu____78321  ->
                                               match uu____78321 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___1987_78351 =
                                                         t3  in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___1987_78351.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___1987_78351.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____78393 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____78393 with
                                  | (bs1,t') ->
                                      let uu____78408 =
                                        let uu____78415 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____78415 ctrl1 t'
                                         in
                                      bind uu____78408
                                        (fun uu____78433  ->
                                           match uu____78433 with
                                           | (t'',ctrl2) ->
                                               let uu____78448 =
                                                 let uu____78455 =
                                                   let uu___2000_78458 = t4
                                                      in
                                                   let uu____78461 =
                                                     let uu____78462 =
                                                       let uu____78481 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____78490 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____78481,
                                                         uu____78490, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____78462
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____78461;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___2000_78458.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___2000_78458.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____78455, ctrl2)  in
                                               ret uu____78448))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____78543 -> ret (t3, ctrl1))))

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
              let uu____78590 = ctrl_tac_fold f env ctrl t  in
              bind uu____78590
                (fun uu____78614  ->
                   match uu____78614 with
                   | (t1,ctrl1) ->
                       let uu____78629 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____78629
                         (fun uu____78656  ->
                            match uu____78656 with
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
                let uu____78750 =
                  let uu____78758 =
                    add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                      opts label1
                     in
                  bind uu____78758
                    (fun uu____78769  ->
                       let uu____78770 = ctrl t1  in
                       bind uu____78770
                         (fun res  ->
                            let uu____78797 = trivial ()  in
                            bind uu____78797 (fun uu____78806  -> ret res)))
                   in
                bind uu____78750
                  (fun uu____78824  ->
                     match uu____78824 with
                     | (should_rewrite,ctrl1) ->
                         if Prims.op_Negation should_rewrite
                         then ret (t1, ctrl1)
                         else
                           (let uu____78853 =
                              FStar_TypeChecker_TcTerm.tc_term
                                (let uu___2037_78862 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___2037_78862.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___2037_78862.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___2037_78862.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___2037_78862.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___2037_78862.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___2037_78862.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___2037_78862.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___2037_78862.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___2037_78862.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___2037_78862.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___2037_78862.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___2037_78862.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___2037_78862.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___2037_78862.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___2037_78862.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___2037_78862.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___2037_78862.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___2037_78862.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___2037_78862.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___2037_78862.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___2037_78862.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___2037_78862.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___2037_78862.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___2037_78862.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___2037_78862.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___2037_78862.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___2037_78862.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___2037_78862.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___2037_78862.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___2037_78862.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___2037_78862.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___2037_78862.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___2037_78862.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___2037_78862.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___2037_78862.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___2037_78862.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___2037_78862.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___2037_78862.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___2037_78862.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___2037_78862.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___2037_78862.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___2037_78862.FStar_TypeChecker_Env.nbe)
                                 }) t1
                               in
                            match uu____78853 with
                            | (t2,lcomp,g) ->
                                let uu____78873 =
                                  (let uu____78877 =
                                     FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                       lcomp
                                      in
                                   Prims.op_Negation uu____78877) ||
                                    (let uu____78880 =
                                       FStar_TypeChecker_Env.is_trivial g  in
                                     Prims.op_Negation uu____78880)
                                   in
                                if uu____78873
                                then ret (t2, globalStop)
                                else
                                  (let typ =
                                     lcomp.FStar_Syntax_Syntax.res_typ  in
                                   let uu____78896 =
                                     new_uvar "pointwise_rec" env typ  in
                                   bind uu____78896
                                     (fun uu____78917  ->
                                        match uu____78917 with
                                        | (ut,uvar_ut) ->
                                            (log ps
                                               (fun uu____78934  ->
                                                  let uu____78935 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t2
                                                     in
                                                  let uu____78937 =
                                                    FStar_Syntax_Print.term_to_string
                                                      ut
                                                     in
                                                  FStar_Util.print2
                                                    "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                    uu____78935 uu____78937);
                                             (let uu____78940 =
                                                let uu____78943 =
                                                  let uu____78944 =
                                                    FStar_TypeChecker_TcTerm.universe_of
                                                      env typ
                                                     in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____78944 typ t2 ut
                                                   in
                                                add_irrelevant_goal
                                                  "rewrite_rec equation" env
                                                  uu____78943 opts label1
                                                 in
                                              bind uu____78940
                                                (fun uu____78952  ->
                                                   let uu____78953 =
                                                     bind rewriter
                                                       (fun uu____78967  ->
                                                          let ut1 =
                                                            FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                              env ut
                                                             in
                                                          log ps
                                                            (fun uu____78973 
                                                               ->
                                                               let uu____78974
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   t2
                                                                  in
                                                               let uu____78976
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   ut1
                                                                  in
                                                               FStar_Util.print2
                                                                 "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                                 uu____78974
                                                                 uu____78976);
                                                          ret (ut1, ctrl1))
                                                      in
                                                   focus uu____78953)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term -> (Prims.bool * FStar_BigInt.t) tac) ->
    unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____79022 =
        bind get
          (fun ps  ->
             let uu____79032 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____79032 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____79070  ->
                       let uu____79071 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____79071);
                  bind dismiss_all
                    (fun uu____79076  ->
                       let uu____79077 =
                         let uu____79084 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____79084
                           keepGoing gt1
                          in
                       bind uu____79077
                         (fun uu____79096  ->
                            match uu____79096 with
                            | (gt',uu____79104) ->
                                (log ps
                                   (fun uu____79108  ->
                                      let uu____79109 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____79109);
                                 (let uu____79112 = push_goals gs  in
                                  bind uu____79112
                                    (fun uu____79117  ->
                                       let uu____79118 =
                                         let uu____79121 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____79121]  in
                                       add_goals uu____79118)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____79022
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____79146 =
        bind get
          (fun ps  ->
             let uu____79156 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____79156 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____79194  ->
                       let uu____79195 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____79195);
                  bind dismiss_all
                    (fun uu____79200  ->
                       let uu____79201 =
                         let uu____79204 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____79204 gt1
                          in
                       bind uu____79201
                         (fun gt'  ->
                            log ps
                              (fun uu____79212  ->
                                 let uu____79213 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____79213);
                            (let uu____79216 = push_goals gs  in
                             bind uu____79216
                               (fun uu____79221  ->
                                  let uu____79222 =
                                    let uu____79225 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____79225]  in
                                  add_goals uu____79222))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____79146
  
let (trefl : unit -> unit tac) =
  fun uu____79238  ->
    let uu____79241 =
      let uu____79244 = cur_goal ()  in
      bind uu____79244
        (fun g  ->
           let uu____79262 =
             let uu____79267 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____79267  in
           match uu____79262 with
           | FStar_Pervasives_Native.Some t ->
               let uu____79275 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____79275 with
                | (hd1,args) ->
                    let uu____79314 =
                      let uu____79327 =
                        let uu____79328 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____79328.FStar_Syntax_Syntax.n  in
                      (uu____79327, args)  in
                    (match uu____79314 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____79342::(l,uu____79344)::(r,uu____79346)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____79393 =
                           let uu____79397 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____79397 l r  in
                         bind uu____79393
                           (fun b  ->
                              if b
                              then solve' g FStar_Syntax_Util.exp_unit
                              else
                                (let l1 =
                                   let uu____79408 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____79408 l
                                    in
                                 let r1 =
                                   let uu____79410 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____79410 r
                                    in
                                 let uu____79411 =
                                   let uu____79415 =
                                     FStar_Tactics_Types.goal_env g  in
                                   do_unify uu____79415 l1 r1  in
                                 bind uu____79411
                                   (fun b1  ->
                                      if b1
                                      then
                                        solve' g FStar_Syntax_Util.exp_unit
                                      else
                                        (let uu____79425 =
                                           let uu____79427 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____79427 l1  in
                                         let uu____79428 =
                                           let uu____79430 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____79430 r1  in
                                         fail2
                                           "not a trivial equality ((%s) vs (%s))"
                                           uu____79425 uu____79428))))
                     | (hd2,uu____79433) ->
                         let uu____79450 =
                           let uu____79452 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____79452 t  in
                         fail1 "trefl: not an equality (%s)" uu____79450))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____79241
  
let (dup : unit -> unit tac) =
  fun uu____79469  ->
    let uu____79472 = cur_goal ()  in
    bind uu____79472
      (fun g  ->
         let uu____79478 =
           let uu____79485 = FStar_Tactics_Types.goal_env g  in
           let uu____79486 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____79485 uu____79486  in
         bind uu____79478
           (fun uu____79496  ->
              match uu____79496 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___2129_79506 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___2129_79506.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___2129_79506.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___2129_79506.FStar_Tactics_Types.is_guard);
                      FStar_Tactics_Types.label =
                        (uu___2129_79506.FStar_Tactics_Types.label)
                    }  in
                  bind __dismiss
                    (fun uu____79509  ->
                       let uu____79510 =
                         let uu____79513 = FStar_Tactics_Types.goal_env g  in
                         let uu____79514 =
                           let uu____79515 =
                             let uu____79516 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____79517 =
                               FStar_Tactics_Types.goal_type g  in
                             FStar_TypeChecker_TcTerm.universe_of uu____79516
                               uu____79517
                              in
                           let uu____79518 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____79519 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____79515 uu____79518 u
                             uu____79519
                            in
                         add_irrelevant_goal "dup equation" uu____79513
                           uu____79514 g.FStar_Tactics_Types.opts
                           g.FStar_Tactics_Types.label
                          in
                       bind uu____79510
                         (fun uu____79523  ->
                            let uu____79524 = add_goals [g']  in
                            bind uu____79524 (fun uu____79528  -> ret ())))))
  
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
              let uu____79654 = f x y  in
              if uu____79654 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____79677 -> (acc, l11, l21)  in
        let uu____79692 = aux [] l1 l2  in
        match uu____79692 with | (pr,t1,t2) -> ((FStar_List.rev pr), t1, t2)
  
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
      let uu____79798 = get_phi g1  in
      match uu____79798 with
      | FStar_Pervasives_Native.None  -> fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____79805 = get_phi g2  in
          (match uu____79805 with
           | FStar_Pervasives_Native.None  -> fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let uu____79818 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2)
                  in
               (match uu____79818 with
                | (gamma,r1,r2) ->
                    let t1 =
                      let uu____79849 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1)
                         in
                      close_forall_no_univs1 uu____79849 phi1  in
                    let t2 =
                      let uu____79859 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2)
                         in
                      close_forall_no_univs1 uu____79859 phi2  in
                    let uu____79868 =
                      set_solution g1 FStar_Syntax_Util.exp_unit  in
                    bind uu____79868
                      (fun uu____79873  ->
                         let uu____79874 =
                           set_solution g2 FStar_Syntax_Util.exp_unit  in
                         bind uu____79874
                           (fun uu____79881  ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2  in
                              let nenv =
                                let uu___2180_79886 =
                                  FStar_Tactics_Types.goal_env g1  in
                                let uu____79887 =
                                  FStar_Util.smap_create
                                    (Prims.parse_int "100")
                                   in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___2180_79886.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___2180_79886.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___2180_79886.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___2180_79886.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____79887;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___2180_79886.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___2180_79886.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___2180_79886.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___2180_79886.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___2180_79886.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___2180_79886.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___2180_79886.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___2180_79886.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___2180_79886.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___2180_79886.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___2180_79886.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___2180_79886.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___2180_79886.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___2180_79886.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___2180_79886.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___2180_79886.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___2180_79886.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___2180_79886.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___2180_79886.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___2180_79886.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___2180_79886.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___2180_79886.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___2180_79886.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___2180_79886.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___2180_79886.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___2180_79886.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___2180_79886.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___2180_79886.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___2180_79886.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___2180_79886.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___2180_79886.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___2180_79886.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___2180_79886.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___2180_79886.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___2180_79886.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___2180_79886.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___2180_79886.FStar_TypeChecker_Env.nbe)
                                }  in
                              let uu____79891 =
                                mk_irrelevant_goal "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                  g1.FStar_Tactics_Types.label
                                 in
                              bind uu____79891
                                (fun goal  ->
                                   mlog
                                     (fun uu____79901  ->
                                        let uu____79902 =
                                          goal_to_string_verbose g1  in
                                        let uu____79904 =
                                          goal_to_string_verbose g2  in
                                        let uu____79906 =
                                          goal_to_string_verbose goal  in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____79902 uu____79904 uu____79906)
                                     (fun uu____79910  -> ret goal))))))
  
let (join : unit -> unit tac) =
  fun uu____79918  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____79934 =
               set
                 (let uu___2195_79939 = ps  in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___2195_79939.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.main_goal =
                      (uu___2195_79939.FStar_Tactics_Types.main_goal);
                    FStar_Tactics_Types.all_implicits =
                      (uu___2195_79939.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___2195_79939.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___2195_79939.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___2195_79939.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___2195_79939.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___2195_79939.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___2195_79939.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___2195_79939.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___2195_79939.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___2195_79939.FStar_Tactics_Types.local_state)
                  })
                in
             bind uu____79934
               (fun uu____79942  ->
                  let uu____79943 = join_goals g1 g2  in
                  bind uu____79943 (fun g12  -> add_goals [g12]))
         | uu____79948 -> fail "join: less than 2 goals")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) tac)
  =
  fun t  ->
    let uu____79970 =
      let uu____79977 = cur_goal ()  in
      bind uu____79977
        (fun g  ->
           let uu____79987 =
             let uu____79996 = FStar_Tactics_Types.goal_env g  in
             __tc uu____79996 t  in
           bind uu____79987
             (fun uu____80024  ->
                match uu____80024 with
                | (t1,typ,guard) ->
                    let uu____80040 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____80040 with
                     | (hd1,args) ->
                         let uu____80089 =
                           let uu____80104 =
                             let uu____80105 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____80105.FStar_Syntax_Syntax.n  in
                           (uu____80104, args)  in
                         (match uu____80089 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____80126)::(q,uu____80128)::[]) when
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
                                let uu____80182 =
                                  let uu____80183 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____80183
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____80182
                                 in
                              let g2 =
                                let uu____80185 =
                                  let uu____80186 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____80186
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____80185
                                 in
                              bind __dismiss
                                (fun uu____80193  ->
                                   let uu____80194 = add_goals [g1; g2]  in
                                   bind uu____80194
                                     (fun uu____80203  ->
                                        let uu____80204 =
                                          let uu____80209 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____80210 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____80209, uu____80210)  in
                                        ret uu____80204))
                          | uu____80215 ->
                              let uu____80230 =
                                let uu____80232 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____80232 typ  in
                              fail1 "Not a disjunction: %s" uu____80230))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____79970
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____80267 =
      let uu____80270 = cur_goal ()  in
      bind uu____80270
        (fun g  ->
           FStar_Options.push ();
           (let uu____80283 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____80283);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___2232_80290 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___2232_80290.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___2232_80290.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___2232_80290.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___2232_80290.FStar_Tactics_Types.label)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____80267
  
let (top_env : unit -> env tac) =
  fun uu____80307  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____80322  ->
    let uu____80326 = cur_goal ()  in
    bind uu____80326
      (fun g  ->
         let uu____80333 =
           (FStar_Options.lax ()) ||
             (let uu____80336 = FStar_Tactics_Types.goal_env g  in
              uu____80336.FStar_TypeChecker_Env.lax)
            in
         ret uu____80333)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____80353 =
        mlog
          (fun uu____80358  ->
             let uu____80359 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____80359)
          (fun uu____80364  ->
             let uu____80365 = cur_goal ()  in
             bind uu____80365
               (fun goal  ->
                  let env =
                    let uu____80373 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____80373 ty  in
                  let uu____80374 = __tc_ghost env tm  in
                  bind uu____80374
                    (fun uu____80393  ->
                       match uu____80393 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____80407  ->
                                let uu____80408 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____80408)
                             (fun uu____80412  ->
                                mlog
                                  (fun uu____80415  ->
                                     let uu____80416 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____80416)
                                  (fun uu____80421  ->
                                     let uu____80422 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____80422
                                       (fun uu____80427  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____80353
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____80452 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____80458 =
              let uu____80465 =
                let uu____80466 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____80466
                 in
              new_uvar "uvar_env.2" env uu____80465  in
            bind uu____80458
              (fun uu____80483  ->
                 match uu____80483 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____80452
        (fun typ  ->
           let uu____80495 = new_uvar "uvar_env" env typ  in
           bind uu____80495
             (fun uu____80510  ->
                match uu____80510 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____80529 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____80548 -> g.FStar_Tactics_Types.opts
             | uu____80551 -> FStar_Options.peek ()  in
           let uu____80554 = FStar_Syntax_Util.head_and_args t  in
           match uu____80554 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____80574);
                FStar_Syntax_Syntax.pos = uu____80575;
                FStar_Syntax_Syntax.vars = uu____80576;_},uu____80577)
               ->
               let env1 =
                 let uu___2286_80619 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___2286_80619.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___2286_80619.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___2286_80619.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___2286_80619.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___2286_80619.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___2286_80619.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___2286_80619.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___2286_80619.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___2286_80619.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___2286_80619.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___2286_80619.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___2286_80619.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___2286_80619.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___2286_80619.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___2286_80619.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___2286_80619.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___2286_80619.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___2286_80619.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___2286_80619.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___2286_80619.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___2286_80619.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___2286_80619.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___2286_80619.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___2286_80619.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___2286_80619.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___2286_80619.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___2286_80619.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___2286_80619.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___2286_80619.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___2286_80619.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___2286_80619.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___2286_80619.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___2286_80619.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___2286_80619.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___2286_80619.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___2286_80619.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___2286_80619.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___2286_80619.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___2286_80619.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___2286_80619.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___2286_80619.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___2286_80619.FStar_TypeChecker_Env.nbe)
                 }  in
               let g =
                 FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false ""  in
               let uu____80623 =
                 let uu____80626 = bnorm_goal g  in [uu____80626]  in
               add_goals uu____80623
           | uu____80627 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____80529
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____80689 = if b then t2 else ret false  in
             bind uu____80689 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____80715 = trytac comp  in
      bind uu____80715
        (fun uu___613_80727  ->
           match uu___613_80727 with
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
        let uu____80769 =
          bind get
            (fun ps  ->
               let uu____80777 = __tc e t1  in
               bind uu____80777
                 (fun uu____80798  ->
                    match uu____80798 with
                    | (t11,ty1,g1) ->
                        let uu____80811 = __tc e t2  in
                        bind uu____80811
                          (fun uu____80832  ->
                             match uu____80832 with
                             | (t21,ty2,g2) ->
                                 let uu____80845 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____80845
                                   (fun uu____80852  ->
                                      let uu____80853 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____80853
                                        (fun uu____80861  ->
                                           let uu____80862 =
                                             do_unify e ty1 ty2  in
                                           let uu____80866 =
                                             do_unify e t11 t21  in
                                           tac_and uu____80862 uu____80866)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____80769
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____80914  ->
             let uu____80915 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____80915
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
        (fun uu____80949  ->
           let uu____80950 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____80950)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____80961 =
      mlog
        (fun uu____80966  ->
           let uu____80967 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____80967)
        (fun uu____80972  ->
           let uu____80973 = cur_goal ()  in
           bind uu____80973
             (fun g  ->
                let uu____80979 =
                  let uu____80988 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____80988 ty  in
                bind uu____80979
                  (fun uu____81000  ->
                     match uu____81000 with
                     | (ty1,uu____81010,guard) ->
                         let uu____81012 =
                           let uu____81015 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____81015 guard  in
                         bind uu____81012
                           (fun uu____81019  ->
                              let uu____81020 =
                                let uu____81024 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____81025 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____81024 uu____81025 ty1  in
                              bind uu____81020
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____81034 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____81034
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops]  in
                                      let ng =
                                        let uu____81041 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____81042 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____81041
                                          uu____81042
                                         in
                                      let nty =
                                        let uu____81044 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____81044 ty1  in
                                      let uu____81045 =
                                        let uu____81049 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____81049 ng nty  in
                                      bind uu____81045
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____81058 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____81058
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____80961
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) Prims.list tac)
  =
  fun s_tm  ->
    let uu____81132 =
      let uu____81141 = cur_goal ()  in
      bind uu____81141
        (fun g  ->
           let uu____81153 =
             let uu____81162 = FStar_Tactics_Types.goal_env g  in
             __tc uu____81162 s_tm  in
           bind uu____81153
             (fun uu____81180  ->
                match uu____81180 with
                | (s_tm1,s_ty,guard) ->
                    let uu____81198 =
                      let uu____81201 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____81201 guard  in
                    bind uu____81198
                      (fun uu____81214  ->
                         let uu____81215 =
                           FStar_Syntax_Util.head_and_args' s_ty  in
                         match uu____81215 with
                         | (h,args) ->
                             let uu____81260 =
                               let uu____81267 =
                                 let uu____81268 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____81268.FStar_Syntax_Syntax.n  in
                               match uu____81267 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____81283;
                                      FStar_Syntax_Syntax.vars = uu____81284;_},us)
                                   -> ret (fv, us)
                               | uu____81294 -> fail "type is not an fv"  in
                             bind uu____81260
                               (fun uu____81315  ->
                                  match uu____81315 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____81331 =
                                        let uu____81334 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____81334 t_lid
                                         in
                                      (match uu____81331 with
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
                                                  (fun uu____81385  ->
                                                     let uu____81386 =
                                                       FStar_Syntax_Subst.open_term
                                                         t_ps t_ty
                                                        in
                                                     match uu____81386 with
                                                     | (t_ps1,t_ty1) ->
                                                         let uu____81401 =
                                                           mapM
                                                             (fun c_lid  ->
                                                                let uu____81429
                                                                  =
                                                                  let uu____81432
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                  FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____81432
                                                                    c_lid
                                                                   in
                                                                match uu____81429
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
                                                                    uu____81506
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
                                                                    let uu____81511
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____81511
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____81534
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____81534
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____81577
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs
                                                                     in
                                                                    (match uu____81577
                                                                    with
                                                                    | 
                                                                    (d_ps,bs1)
                                                                    ->
                                                                    let uu____81650
                                                                    =
                                                                    let uu____81652
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp  in
                                                                    Prims.op_Negation
                                                                    uu____81652
                                                                     in
                                                                    failwhen
                                                                    uu____81650
                                                                    "not total?"
                                                                    (fun
                                                                    uu____81671
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
                                                                    uu___614_81688
                                                                    =
                                                                    match uu___614_81688
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____81692)
                                                                    -> true
                                                                    | 
                                                                    uu____81695
                                                                    -> false
                                                                     in
                                                                    let uu____81699
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____81699
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
                                                                    uu____81833
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
                                                                    uu____81895
                                                                     ->
                                                                    match uu____81895
                                                                    with
                                                                    | 
                                                                    ((bv,uu____81915),
                                                                    (t,uu____81917))
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
                                                                    uu____81987
                                                                     ->
                                                                    match uu____81987
                                                                    with
                                                                    | 
                                                                    ((bv,uu____82014),
                                                                    (t,uu____82016))
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
                                                                    uu____82075
                                                                     ->
                                                                    match uu____82075
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
                                                                    let uu____82130
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___2450_82147
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___2450_82147.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___2450_82147.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___2450_82147.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___2450_82147.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___2450_82147.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___2450_82147.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___2450_82147.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___2450_82147.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___2450_82147.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___2450_82147.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___2450_82147.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___2450_82147.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___2450_82147.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___2450_82147.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___2450_82147.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___2450_82147.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___2450_82147.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___2450_82147.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___2450_82147.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___2450_82147.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___2450_82147.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___2450_82147.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___2450_82147.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___2450_82147.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___2450_82147.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___2450_82147.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___2450_82147.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___2450_82147.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___2450_82147.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___2450_82147.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___2450_82147.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___2450_82147.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___2450_82147.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___2450_82147.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___2450_82147.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___2450_82147.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___2450_82147.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___2450_82147.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___2450_82147.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___2450_82147.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___2450_82147.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___2450_82147.FStar_TypeChecker_Env.nbe)
                                                                    }) s_ty
                                                                    pat  in
                                                                    match uu____82130
                                                                    with
                                                                    | 
                                                                    (uu____82161,uu____82162,uu____82163,pat_t,uu____82165,_guard_pat)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____82172
                                                                    =
                                                                    let uu____82173
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____82173
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____82172
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____82178
                                                                    =
                                                                    let uu____82187
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____82187]
                                                                     in
                                                                    let uu____82206
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____82178
                                                                    uu____82206
                                                                     in
                                                                    let nty =
                                                                    let uu____82212
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____82212
                                                                     in
                                                                    let uu____82215
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____82215
                                                                    (fun
                                                                    uu____82245
                                                                     ->
                                                                    match uu____82245
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
                                                                    let uu____82272
                                                                    =
                                                                    let uu____82283
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____82283]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____82272
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____82319
                                                                    =
                                                                    let uu____82330
                                                                    =
                                                                    let uu____82335
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2)  in
                                                                    (fv1,
                                                                    uu____82335)
                                                                     in
                                                                    (g', br,
                                                                    uu____82330)
                                                                     in
                                                                    ret
                                                                    uu____82319))))))
                                                                    | 
                                                                    uu____82356
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                             c_lids
                                                            in
                                                         bind uu____81401
                                                           (fun goal_brs  ->
                                                              let uu____82406
                                                                =
                                                                FStar_List.unzip3
                                                                  goal_brs
                                                                 in
                                                              match uu____82406
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
                                                                  let uu____82479
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                  bind
                                                                    uu____82479
                                                                    (
                                                                    fun
                                                                    uu____82490
                                                                     ->
                                                                    let uu____82491
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____82491
                                                                    (fun
                                                                    uu____82501
                                                                     ->
                                                                    ret infos))))
                                            | uu____82508 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____81132
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____82557::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____82587 = init xs  in x :: uu____82587
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____82600 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      let t3 = FStar_Syntax_Util.unlazy_emb t2  in
      match t3.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____82609) -> inspect t4
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____82675 = last args  in
          (match uu____82675 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____82705 =
                 let uu____82706 =
                   let uu____82711 =
                     let uu____82712 =
                       let uu____82717 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____82717  in
                     uu____82712 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____82711, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____82706  in
               FStar_All.pipe_left ret uu____82705)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____82730,uu____82731) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
          let uu____82784 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____82784 with
           | (bs1,t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____82826 =
                      let uu____82827 =
                        let uu____82832 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____82832)  in
                      FStar_Reflection_Data.Tv_Abs uu____82827  in
                    FStar_All.pipe_left ret uu____82826))
      | FStar_Syntax_Syntax.Tm_type uu____82835 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____82860 ->
          let uu____82875 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____82875 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____82906 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____82906 with
           | (b',t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____82959 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____82972 =
            let uu____82973 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____82973  in
          FStar_All.pipe_left ret uu____82972
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____82994 =
            let uu____82995 =
              let uu____83000 =
                let uu____83001 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____83001  in
              (uu____83000, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____82995  in
          FStar_All.pipe_left ret uu____82994
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____83041 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____83046 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____83046 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____83099 ->
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
             | FStar_Util.Inr uu____83141 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____83145 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____83145 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____83165 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____83171 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____83226 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____83226
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____83247 =
                  let uu____83254 =
                    FStar_List.map
                      (fun uu____83267  ->
                         match uu____83267 with
                         | (p1,uu____83276) -> inspect_pat p1) ps
                     in
                  (fv, uu____83254)  in
                FStar_Reflection_Data.Pat_Cons uu____83247
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
              (fun uu___615_83372  ->
                 match uu___615_83372 with
                 | (pat,uu____83394,t5) ->
                     let uu____83412 = inspect_pat pat  in (uu____83412, t5))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____83421 ->
          ((let uu____83423 =
              let uu____83429 =
                let uu____83431 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____83433 = FStar_Syntax_Print.term_to_string t3  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____83431 uu____83433
                 in
              (FStar_Errors.Warning_CantInspect, uu____83429)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____83423);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____82600
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____83451 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____83451
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____83455 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____83455
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____83459 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____83459
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____83466 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____83466
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____83491 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____83491
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____83508 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____83508
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____83527 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____83527
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____83531 =
          let uu____83532 =
            let uu____83539 =
              let uu____83540 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____83540  in
            FStar_Syntax_Syntax.mk uu____83539  in
          uu____83532 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____83531
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____83548 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____83548
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____83559 =
          let uu____83560 =
            let uu____83567 =
              let uu____83568 =
                let uu____83582 =
                  let uu____83585 =
                    let uu____83586 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____83586]  in
                  FStar_Syntax_Subst.close uu____83585 t2  in
                ((false, [lb]), uu____83582)  in
              FStar_Syntax_Syntax.Tm_let uu____83568  in
            FStar_Syntax_Syntax.mk uu____83567  in
          uu____83560 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____83559
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____83631 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____83631 with
         | (lbs,body) ->
             let uu____83646 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____83646)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____83683 =
                let uu____83684 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____83684  in
              FStar_All.pipe_left wrap uu____83683
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____83691 =
                let uu____83692 =
                  let uu____83706 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____83724 = pack_pat p1  in
                         (uu____83724, false)) ps
                     in
                  (fv, uu____83706)  in
                FStar_Syntax_Syntax.Pat_cons uu____83692  in
              FStar_All.pipe_left wrap uu____83691
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
            (fun uu___616_83773  ->
               match uu___616_83773 with
               | (pat,t1) ->
                   let uu____83790 = pack_pat pat  in
                   (uu____83790, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____83838 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____83838
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____83866 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____83866
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____83912 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____83912
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____83951 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____83951
  
let (lget :
  FStar_Reflection_Data.typ -> Prims.string -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun k  ->
      let uu____83971 =
        bind get
          (fun ps  ->
             let uu____83977 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____83977 with
             | FStar_Pervasives_Native.None  -> fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
      FStar_All.pipe_left (wrap_err "lget") uu____83971
  
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit tac)
  =
  fun _ty  ->
    fun k  ->
      fun t  ->
        let uu____84011 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___2748_84018 = ps  in
                 let uu____84019 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t
                    in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___2748_84018.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___2748_84018.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___2748_84018.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___2748_84018.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___2748_84018.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___2748_84018.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___2748_84018.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___2748_84018.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___2748_84018.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___2748_84018.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___2748_84018.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___2748_84018.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____84019
                 }  in
               set ps1)
           in
        FStar_All.pipe_left (wrap_err "lset") uu____84011
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal * FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun typ  ->
      let uu____84046 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____84046 with
      | (u,ctx_uvars,g_u) ->
          let uu____84079 = FStar_List.hd ctx_uvars  in
          (match uu____84079 with
           | (ctx_uvar,uu____84093) ->
               let g =
                 let uu____84095 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____84095 false
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
        let uu____84118 = goal_of_goal_ty env typ  in
        match uu____84118 with
        | (g,g_u) ->
            let ps =
              let uu____84130 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "TacVerbose")
                 in
              let uu____84133 = FStar_Util.psmap_empty ()  in
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
                FStar_Tactics_Types.tac_verb_dbg = uu____84130;
                FStar_Tactics_Types.local_state = uu____84133
              }  in
            let uu____84143 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____84143)
  