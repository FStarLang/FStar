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
    let uu____68712 =
      let uu____68713 = FStar_Tactics_Types.goal_env g  in
      let uu____68714 = FStar_Tactics_Types.goal_type g  in
      bnorm uu____68713 uu____68714  in
    FStar_Tactics_Types.goal_with_type g uu____68712
  
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
      let uu____68828 = FStar_Options.tactics_failhard ()  in
      if uu____68828
      then run t p
      else
        (try (fun uu___640_68838  -> match () with | () -> run t p) ()
         with
         | FStar_Errors.Err (uu____68847,msg) ->
             FStar_Tactics_Result.Failed
               ((FStar_Tactics_Types.TacticFailure msg), p)
         | FStar_Errors.Error (uu____68851,msg,uu____68853) ->
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
           let uu____68933 = run t1 p  in
           match uu____68933 with
           | FStar_Tactics_Result.Success (a,q) ->
               let uu____68940 = t2 a  in run uu____68940 q
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
    let uu____68963 =
      FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head  in
    match uu____68963 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (check_goal_solved :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun goal  -> get_uvar_solved goal.FStar_Tactics_Types.goal_ctx_uvar 
let (goal_to_string_verbose : FStar_Tactics_Types.goal -> Prims.string) =
  fun g  ->
    let uu____68985 =
      FStar_Syntax_Print.ctx_uvar_to_string
        g.FStar_Tactics_Types.goal_ctx_uvar
       in
    let uu____68987 =
      let uu____68989 = check_goal_solved g  in
      match uu____68989 with
      | FStar_Pervasives_Native.None  -> ""
      | FStar_Pervasives_Native.Some t ->
          let uu____68995 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "\tGOAL ALREADY SOLVED!: %s" uu____68995
       in
    FStar_Util.format2 "%s%s\n" uu____68985 uu____68987
  
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
            let uu____69042 = FStar_Options.print_implicits ()  in
            if uu____69042
            then
              let uu____69046 = FStar_Tactics_Types.goal_env g  in
              let uu____69047 = FStar_Tactics_Types.goal_witness g  in
              tts uu____69046 uu____69047
            else
              (let uu____69050 =
                 get_uvar_solved g.FStar_Tactics_Types.goal_ctx_uvar  in
               match uu____69050 with
               | FStar_Pervasives_Native.None  -> "_"
               | FStar_Pervasives_Native.Some t ->
                   let uu____69056 = FStar_Tactics_Types.goal_env g  in
                   let uu____69057 = FStar_Tactics_Types.goal_witness g  in
                   tts uu____69056 uu____69057)
             in
          let num =
            match maybe_num with
            | FStar_Pervasives_Native.None  -> ""
            | FStar_Pervasives_Native.Some (i,n1) ->
                let uu____69080 = FStar_Util.string_of_int i  in
                let uu____69082 = FStar_Util.string_of_int n1  in
                FStar_Util.format2 " %s/%s" uu____69080 uu____69082
             in
          let maybe_label =
            match g.FStar_Tactics_Types.label with
            | "" -> ""
            | l -> Prims.op_Hat " (" (Prims.op_Hat l ")")  in
          let actual_goal =
            if ps.FStar_Tactics_Types.tac_verb_dbg
            then goal_to_string_verbose g
            else
              (let uu____69100 =
                 FStar_Syntax_Print.binders_to_string ", "
                   (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
                  in
               let uu____69103 =
                 let uu____69105 = FStar_Tactics_Types.goal_env g  in
                 tts uu____69105
                   (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                  in
               FStar_Util.format3 "%s |- %s : %s\n" uu____69100 w uu____69103)
             in
          FStar_Util.format4 "%s%s%s:\n%s\n" kind num maybe_label actual_goal
  
let (tacprint : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      let uu____69132 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____69132
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____69157 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____69157
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____69189 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____69189
  
let (comp_to_typ : FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____69199) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____69209) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (get_phi :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun g  ->
    let uu____69229 =
      let uu____69230 = FStar_Tactics_Types.goal_env g  in
      let uu____69231 = FStar_Tactics_Types.goal_type g  in
      FStar_TypeChecker_Normalize.unfold_whnf uu____69230 uu____69231  in
    FStar_Syntax_Util.un_squash uu____69229
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  -> let uu____69240 = get_phi g  in FStar_Option.isSome uu____69240 
let (print : Prims.string -> unit tac) = fun msg  -> tacprint msg; ret () 
let (debugging : unit -> Prims.bool tac) =
  fun uu____69264  ->
    bind get
      (fun ps  ->
         let uu____69272 =
           FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
             (FStar_Options.Other "Tac")
            in
         ret uu____69272)
  
let (ps_to_string :
  (Prims.string * FStar_Tactics_Types.proofstate) -> Prims.string) =
  fun uu____69287  ->
    match uu____69287 with
    | (msg,ps) ->
        let p_imp imp =
          FStar_Syntax_Print.uvar_to_string
            (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
           in
        let n_active = FStar_List.length ps.FStar_Tactics_Types.goals  in
        let n_smt = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
        let n1 = n_active + n_smt  in
        let uu____69319 =
          let uu____69323 =
            let uu____69327 =
              let uu____69329 =
                FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
              FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____69329
                msg
               in
            let uu____69332 =
              let uu____69336 =
                if
                  ps.FStar_Tactics_Types.entry_range <>
                    FStar_Range.dummyRange
                then
                  let uu____69340 =
                    FStar_Range.string_of_def_range
                      ps.FStar_Tactics_Types.entry_range
                     in
                  FStar_Util.format1 "Location: %s\n" uu____69340
                else ""  in
              let uu____69346 =
                let uu____69350 =
                  let uu____69352 =
                    FStar_TypeChecker_Env.debug
                      ps.FStar_Tactics_Types.main_context
                      (FStar_Options.Other "Imp")
                     in
                  if uu____69352
                  then
                    let uu____69357 =
                      FStar_Common.string_of_list p_imp
                        ps.FStar_Tactics_Types.all_implicits
                       in
                    FStar_Util.format1 "Imps: %s\n" uu____69357
                  else ""  in
                [uu____69350]  in
              uu____69336 :: uu____69346  in
            uu____69327 :: uu____69332  in
          let uu____69367 =
            let uu____69371 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "Goal"
                       (FStar_Pervasives_Native.Some
                          (((Prims.parse_int "1") + i), n1)) ps g)
                ps.FStar_Tactics_Types.goals
               in
            let uu____69391 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "SMT Goal"
                       (FStar_Pervasives_Native.Some
                          ((((Prims.parse_int "1") + n_active) + i), n1)) ps
                       g) ps.FStar_Tactics_Types.smt_goals
               in
            FStar_List.append uu____69371 uu____69391  in
          FStar_List.append uu____69323 uu____69367  in
        FStar_String.concat "" uu____69319
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      let uu____69425 =
        let uu____69426 = FStar_Tactics_Types.goal_env g  in
        FStar_TypeChecker_Env.all_binders uu____69426  in
      let uu____69427 =
        let uu____69432 =
          let uu____69433 = FStar_Tactics_Types.goal_env g  in
          FStar_TypeChecker_Env.dsenv uu____69433  in
        FStar_Syntax_Print.binders_to_json uu____69432  in
      FStar_All.pipe_right uu____69425 uu____69427  in
    let uu____69434 =
      let uu____69442 =
        let uu____69450 =
          let uu____69456 =
            let uu____69457 =
              let uu____69465 =
                let uu____69471 =
                  let uu____69472 =
                    let uu____69474 = FStar_Tactics_Types.goal_env g  in
                    let uu____69475 = FStar_Tactics_Types.goal_witness g  in
                    tts uu____69474 uu____69475  in
                  FStar_Util.JsonStr uu____69472  in
                ("witness", uu____69471)  in
              let uu____69478 =
                let uu____69486 =
                  let uu____69492 =
                    let uu____69493 =
                      let uu____69495 = FStar_Tactics_Types.goal_env g  in
                      let uu____69496 = FStar_Tactics_Types.goal_type g  in
                      tts uu____69495 uu____69496  in
                    FStar_Util.JsonStr uu____69493  in
                  ("type", uu____69492)  in
                [uu____69486;
                ("label", (FStar_Util.JsonStr (g.FStar_Tactics_Types.label)))]
                 in
              uu____69465 :: uu____69478  in
            FStar_Util.JsonAssoc uu____69457  in
          ("goal", uu____69456)  in
        [uu____69450]  in
      ("hyps", g_binders) :: uu____69442  in
    FStar_Util.JsonAssoc uu____69434
  
let (ps_to_json :
  (Prims.string * FStar_Tactics_Types.proofstate) -> FStar_Util.json) =
  fun uu____69550  ->
    match uu____69550 with
    | (msg,ps) ->
        let uu____69560 =
          let uu____69568 =
            let uu____69576 =
              let uu____69584 =
                let uu____69592 =
                  let uu____69598 =
                    let uu____69599 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____69599  in
                  ("goals", uu____69598)  in
                let uu____69604 =
                  let uu____69612 =
                    let uu____69618 =
                      let uu____69619 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____69619  in
                    ("smt-goals", uu____69618)  in
                  [uu____69612]  in
                uu____69592 :: uu____69604  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____69584
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____69576  in
          let uu____69653 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____69669 =
                let uu____69675 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____69675)  in
              [uu____69669]
            else []  in
          FStar_List.append uu____69568 uu____69653  in
        FStar_Util.JsonAssoc uu____69560
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____69715  ->
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
         (let uu____69746 = FStar_Tactics_Types.subst_proof_state subst1 ps
             in
          dump_proofstate uu____69746 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let traise : 'a . Prims.exn -> 'a tac =
  fun e  -> mk_tac (fun ps  -> FStar_Tactics_Result.Failed (e, ps)) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____69819 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____69819
          then dump_proofstate ps (Prims.op_Hat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed
           ((FStar_Tactics_Types.TacticFailure msg), ps))
  
let fail1 : 'Auu____69833 . Prims.string -> Prims.string -> 'Auu____69833 tac
  =
  fun msg  ->
    fun x  -> let uu____69850 = FStar_Util.format1 msg x  in fail uu____69850
  
let fail2 :
  'Auu____69861 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____69861 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        let uu____69885 = FStar_Util.format2 msg x y  in fail uu____69885
  
let fail3 :
  'Auu____69898 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____69898 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____69929 = FStar_Util.format3 msg x y z  in fail uu____69929
  
let fail4 :
  'Auu____69944 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____69944 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____69982 = FStar_Util.format4 msg x y z w  in
            fail uu____69982
  
let catch : 'a . 'a tac -> (Prims.exn,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____70017 = run t ps  in
         match uu____70017 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___802_70041 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___802_70041.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___802_70041.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___802_70041.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___802_70041.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___802_70041.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___802_70041.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___802_70041.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___802_70041.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___802_70041.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___802_70041.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___802_70041.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (uu___802_70041.FStar_Tactics_Types.local_state)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let recover : 'a . 'a tac -> (Prims.exn,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let uu____70080 = run t ps  in
         match uu____70080 with
         | FStar_Tactics_Result.Success (a,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inr a), q)
         | FStar_Tactics_Result.Failed (m,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inl m), q))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____70128 = catch t  in
    bind uu____70128
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____70155 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try
           (fun uu___828_70187  ->
              match () with
              | () -> let uu____70192 = trytac t  in run uu____70192 ps) ()
         with
         | FStar_Errors.Err (uu____70208,msg) ->
             (log ps
                (fun uu____70214  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____70220,msg,uu____70222) ->
             (log ps
                (fun uu____70227  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____70264 = run t ps  in
           match uu____70264 with
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
  fun p  -> mk_tac (fun uu____70288  -> FStar_Tactics_Result.Success ((), p)) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___863_70303 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___863_70303.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___863_70303.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___863_70303.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___863_70303.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___863_70303.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___863_70303.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___863_70303.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___863_70303.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___863_70303.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___863_70303.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___863_70303.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___863_70303.FStar_Tactics_Types.local_state)
            }))
  
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____70327 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____70327
         then
           let uu____70331 = FStar_Syntax_Print.term_to_string t1  in
           let uu____70333 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____70331
             uu____70333
         else ());
        (try
           (fun uu___871_70344  ->
              match () with
              | () ->
                  let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
                  ((let uu____70352 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____70352
                    then
                      let uu____70356 =
                        FStar_Common.string_of_option
                          (FStar_TypeChecker_Rel.guard_to_string env) res
                         in
                      let uu____70358 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____70360 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.print3
                        "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____70356
                        uu____70358 uu____70360
                    else ());
                   (match res with
                    | FStar_Pervasives_Native.None  -> ret false
                    | FStar_Pervasives_Native.Some g ->
                        let uu____70371 =
                          add_implicits g.FStar_TypeChecker_Env.implicits  in
                        bind uu____70371 (fun uu____70376  -> ret true)))) ()
         with
         | FStar_Errors.Err (uu____70386,msg) ->
             mlog
               (fun uu____70392  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____70395  -> ret false)
         | FStar_Errors.Error (uu____70398,msg,r) ->
             mlog
               (fun uu____70406  ->
                  let uu____70407 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____70407) (fun uu____70411  -> ret false))
  
let (compress_implicits : unit tac) =
  bind get
    (fun ps  ->
       let imps = ps.FStar_Tactics_Types.all_implicits  in
       let g =
         let uu___897_70425 = FStar_TypeChecker_Env.trivial_guard  in
         {
           FStar_TypeChecker_Env.guard_f =
             (uu___897_70425.FStar_TypeChecker_Env.guard_f);
           FStar_TypeChecker_Env.deferred =
             (uu___897_70425.FStar_TypeChecker_Env.deferred);
           FStar_TypeChecker_Env.univ_ineqs =
             (uu___897_70425.FStar_TypeChecker_Env.univ_ineqs);
           FStar_TypeChecker_Env.implicits = imps
         }  in
       let g1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g
          in
       let ps' =
         let uu___901_70428 = ps  in
         {
           FStar_Tactics_Types.main_context =
             (uu___901_70428.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___901_70428.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (g1.FStar_TypeChecker_Env.implicits);
           FStar_Tactics_Types.goals =
             (uu___901_70428.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___901_70428.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___901_70428.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___901_70428.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___901_70428.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___901_70428.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___901_70428.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___901_70428.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___901_70428.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___901_70428.FStar_Tactics_Types.local_state)
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
          (fun uu____70455  ->
             (let uu____70457 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____70457
              then
                (FStar_Options.push ();
                 (let uu____70462 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____70466 = __do_unify env t1 t2  in
              bind uu____70466
                (fun r  ->
                   (let uu____70477 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____70477 then FStar_Options.pop () else ());
                   ret r)))
  
let (remove_solved_goals : unit tac) =
  bind get
    (fun ps  ->
       let ps' =
         let uu___916_70491 = ps  in
         let uu____70492 =
           FStar_List.filter
             (fun g  ->
                let uu____70498 = check_goal_solved g  in
                FStar_Option.isNone uu____70498) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___916_70491.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___916_70491.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___916_70491.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____70492;
           FStar_Tactics_Types.smt_goals =
             (uu___916_70491.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___916_70491.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___916_70491.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___916_70491.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___916_70491.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___916_70491.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___916_70491.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___916_70491.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___916_70491.FStar_Tactics_Types.local_state)
         }  in
       set ps')
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____70516 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____70516 with
      | FStar_Pervasives_Native.Some uu____70521 ->
          let uu____70522 =
            let uu____70524 = goal_to_string_verbose goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____70524  in
          fail uu____70522
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____70545 = FStar_Tactics_Types.goal_env goal  in
      let uu____70546 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____70545 solution uu____70546
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____70553 =
         let uu___929_70554 = p  in
         let uu____70555 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___929_70554.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___929_70554.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___929_70554.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____70555;
           FStar_Tactics_Types.smt_goals =
             (uu___929_70554.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___929_70554.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___929_70554.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___929_70554.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___929_70554.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___929_70554.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___929_70554.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___929_70554.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___929_70554.FStar_Tactics_Types.local_state)
         }  in
       set uu____70553)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      mlog
        (fun uu____70577  ->
           let uu____70578 =
             let uu____70580 = FStar_Tactics_Types.goal_witness goal  in
             FStar_Syntax_Print.term_to_string uu____70580  in
           let uu____70581 = FStar_Syntax_Print.term_to_string solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____70578 uu____70581)
        (fun uu____70586  ->
           let uu____70587 = trysolve goal solution  in
           bind uu____70587
             (fun b  ->
                if b
                then bind __dismiss (fun uu____70599  -> remove_solved_goals)
                else
                  (let uu____70602 =
                     let uu____70604 =
                       let uu____70606 = FStar_Tactics_Types.goal_env goal
                          in
                       tts uu____70606 solution  in
                     let uu____70607 =
                       let uu____70609 = FStar_Tactics_Types.goal_env goal
                          in
                       let uu____70610 =
                         FStar_Tactics_Types.goal_witness goal  in
                       tts uu____70609 uu____70610  in
                     let uu____70611 =
                       let uu____70613 = FStar_Tactics_Types.goal_env goal
                          in
                       let uu____70614 = FStar_Tactics_Types.goal_type goal
                          in
                       tts uu____70613 uu____70614  in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____70604 uu____70607 uu____70611
                      in
                   fail uu____70602)))
  
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____70631 = set_solution goal solution  in
      bind uu____70631
        (fun uu____70635  ->
           bind __dismiss (fun uu____70637  -> remove_solved_goals))
  
let (set_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___945_70656 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___945_70656.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___945_70656.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___945_70656.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals = gs;
              FStar_Tactics_Types.smt_goals =
                (uu___945_70656.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___945_70656.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___945_70656.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___945_70656.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___945_70656.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___945_70656.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___945_70656.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___945_70656.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___945_70656.FStar_Tactics_Types.local_state)
            }))
  
let (set_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___949_70675 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___949_70675.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___949_70675.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___949_70675.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___949_70675.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals = gs;
              FStar_Tactics_Types.depth =
                (uu___949_70675.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___949_70675.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___949_70675.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___949_70675.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___949_70675.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___949_70675.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___949_70675.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___949_70675.FStar_Tactics_Types.local_state)
            }))
  
let (dismiss_all : unit tac) = set_goals [] 
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____70702 = FStar_Options.defensive ()  in
    if uu____70702
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____70712 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____70712)
         in
      let b2 =
        b1 &&
          (let uu____70716 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____70716)
         in
      let rec aux b3 e =
        let uu____70731 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____70731 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____70751 =
        (let uu____70755 = aux b2 env  in Prims.op_Negation uu____70755) &&
          (let uu____70758 = FStar_ST.op_Bang nwarn  in
           uu____70758 < (Prims.parse_int "5"))
         in
      (if uu____70751
       then
         ((let uu____70784 =
             let uu____70785 = FStar_Tactics_Types.goal_type g  in
             uu____70785.FStar_Syntax_Syntax.pos  in
           let uu____70788 =
             let uu____70794 =
               let uu____70796 = goal_to_string_verbose g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____70796
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____70794)  in
           FStar_Errors.log_issue uu____70784 uu____70788);
          (let uu____70800 =
             let uu____70802 = FStar_ST.op_Bang nwarn  in
             uu____70802 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____70800))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___971_70871 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___971_70871.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___971_70871.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___971_70871.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___971_70871.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___971_70871.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___971_70871.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___971_70871.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___971_70871.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___971_70871.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___971_70871.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___971_70871.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___971_70871.FStar_Tactics_Types.local_state)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___976_70892 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___976_70892.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___976_70892.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___976_70892.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___976_70892.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___976_70892.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___976_70892.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___976_70892.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___976_70892.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___976_70892.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___976_70892.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___976_70892.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___976_70892.FStar_Tactics_Types.local_state)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___981_70913 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___981_70913.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___981_70913.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___981_70913.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___981_70913.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___981_70913.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___981_70913.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___981_70913.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___981_70913.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___981_70913.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___981_70913.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___981_70913.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___981_70913.FStar_Tactics_Types.local_state)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___986_70934 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___986_70934.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___986_70934.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___986_70934.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___986_70934.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___986_70934.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___986_70934.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___986_70934.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___986_70934.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___986_70934.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___986_70934.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___986_70934.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___986_70934.FStar_Tactics_Types.local_state)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____70946  -> add_goals [g]) 
let (new_uvar :
  Prims.string ->
    env ->
      FStar_Reflection_Data.typ ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar) tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____70977 =
          FStar_TypeChecker_Env.new_implicit_var_aux reason
            typ.FStar_Syntax_Syntax.pos env typ
            FStar_Syntax_Syntax.Allow_untyped FStar_Pervasives_Native.None
           in
        match uu____70977 with
        | (u,ctx_uvar,g_u) ->
            let uu____71015 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____71015
              (fun uu____71024  ->
                 let uu____71025 =
                   let uu____71030 =
                     let uu____71031 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____71031  in
                   (u, uu____71030)  in
                 ret uu____71025)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____71052 = FStar_Syntax_Util.un_squash t1  in
    match uu____71052 with
    | FStar_Pervasives_Native.Some t' ->
        let t'1 = FStar_Syntax_Util.unascribe t'  in
        let uu____71064 =
          let uu____71065 = FStar_Syntax_Subst.compress t'1  in
          uu____71065.FStar_Syntax_Syntax.n  in
        (match uu____71064 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____71070 -> false)
    | uu____71072 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____71085 = FStar_Syntax_Util.un_squash t  in
    match uu____71085 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____71096 =
          let uu____71097 = FStar_Syntax_Subst.compress t'  in
          uu____71097.FStar_Syntax_Syntax.n  in
        (match uu____71096 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____71102 -> false)
    | uu____71104 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____71117  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____71129 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____71129 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____71136 = goal_to_string_verbose hd1  in
                    let uu____71138 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____71136 uu____71138);
                   ret hd1)))
  
let (tadmit_t : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____71151 =
      bind get
        (fun ps  ->
           let uu____71157 = cur_goal ()  in
           bind uu____71157
             (fun g  ->
                (let uu____71164 =
                   let uu____71165 = FStar_Tactics_Types.goal_type g  in
                   uu____71165.FStar_Syntax_Syntax.pos  in
                 let uu____71168 =
                   let uu____71174 =
                     let uu____71176 =
                       goal_to_string "" FStar_Pervasives_Native.None ps g
                        in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____71176
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____71174)  in
                 FStar_Errors.log_issue uu____71164 uu____71168);
                solve' g t))
       in
    FStar_All.pipe_left (wrap_err "tadmit_t") uu____71151
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____71199  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___1031_71210 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___1031_71210.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___1031_71210.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___1031_71210.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___1031_71210.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___1031_71210.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___1031_71210.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___1031_71210.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___1031_71210.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___1031_71210.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___1031_71210.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___1031_71210.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (uu___1031_71210.FStar_Tactics_Types.local_state)
           }  in
         let uu____71212 = set ps1  in
         bind uu____71212
           (fun uu____71217  ->
              let uu____71218 = FStar_BigInt.of_int_fs n1  in ret uu____71218))
  
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
              let uu____71256 = env.FStar_TypeChecker_Env.universe_of env phi
                 in
              FStar_Syntax_Util.mk_squash uu____71256 phi  in
            let uu____71257 = new_uvar reason env typ  in
            bind uu____71257
              (fun uu____71272  ->
                 match uu____71272 with
                 | (uu____71279,ctx_uvar) ->
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
             (fun uu____71326  ->
                let uu____71327 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____71327)
             (fun uu____71332  ->
                let e1 =
                  let uu___1049_71334 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1049_71334.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1049_71334.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1049_71334.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1049_71334.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1049_71334.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1049_71334.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1049_71334.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1049_71334.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1049_71334.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1049_71334.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1049_71334.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1049_71334.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1049_71334.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1049_71334.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1049_71334.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1049_71334.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1049_71334.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1049_71334.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1049_71334.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1049_71334.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1049_71334.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1049_71334.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1049_71334.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1049_71334.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1049_71334.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1049_71334.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1049_71334.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1049_71334.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1049_71334.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1049_71334.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1049_71334.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1049_71334.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1049_71334.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1049_71334.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1049_71334.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1049_71334.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1049_71334.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1049_71334.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1049_71334.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1049_71334.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1049_71334.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1049_71334.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___1053_71346  ->
                     match () with
                     | () ->
                         let uu____71355 =
                           FStar_TypeChecker_TcTerm.type_of_tot_term e1 t  in
                         ret uu____71355) ()
                with
                | FStar_Errors.Err (uu____71382,msg) ->
                    let uu____71386 = tts e1 t  in
                    let uu____71388 =
                      let uu____71390 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____71390
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____71386 uu____71388 msg
                | FStar_Errors.Error (uu____71400,msg,uu____71402) ->
                    let uu____71405 = tts e1 t  in
                    let uu____71407 =
                      let uu____71409 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____71409
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____71405 uu____71407 msg))
  
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
             (fun uu____71462  ->
                let uu____71463 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc_ghost(%s)\n" uu____71463)
             (fun uu____71468  ->
                let e1 =
                  let uu___1070_71470 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1070_71470.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1070_71470.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1070_71470.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1070_71470.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1070_71470.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1070_71470.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1070_71470.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1070_71470.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1070_71470.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1070_71470.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1070_71470.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1070_71470.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1070_71470.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1070_71470.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1070_71470.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1070_71470.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1070_71470.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1070_71470.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1070_71470.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1070_71470.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1070_71470.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1070_71470.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1070_71470.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1070_71470.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1070_71470.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1070_71470.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1070_71470.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1070_71470.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1070_71470.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1070_71470.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1070_71470.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1070_71470.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1070_71470.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1070_71470.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1070_71470.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1070_71470.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1070_71470.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1070_71470.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1070_71470.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1070_71470.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1070_71470.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1070_71470.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___1074_71485  ->
                     match () with
                     | () ->
                         let uu____71494 =
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e1 t
                            in
                         (match uu____71494 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____71532,msg) ->
                    let uu____71536 = tts e1 t  in
                    let uu____71538 =
                      let uu____71540 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____71540
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____71536 uu____71538 msg
                | FStar_Errors.Error (uu____71550,msg,uu____71552) ->
                    let uu____71555 = tts e1 t  in
                    let uu____71557 =
                      let uu____71559 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____71559
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____71555 uu____71557 msg))
  
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
             (fun uu____71612  ->
                let uu____71613 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____71613)
             (fun uu____71619  ->
                let e1 =
                  let uu___1095_71621 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1095_71621.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1095_71621.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1095_71621.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1095_71621.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1095_71621.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1095_71621.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1095_71621.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1095_71621.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1095_71621.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1095_71621.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1095_71621.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1095_71621.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1095_71621.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1095_71621.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1095_71621.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1095_71621.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1095_71621.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1095_71621.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1095_71621.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1095_71621.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1095_71621.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1095_71621.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1095_71621.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1095_71621.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1095_71621.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1095_71621.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1095_71621.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1095_71621.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1095_71621.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1095_71621.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1095_71621.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1095_71621.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1095_71621.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1095_71621.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1095_71621.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1095_71621.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1095_71621.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1095_71621.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1095_71621.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1095_71621.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1095_71621.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1095_71621.FStar_TypeChecker_Env.nbe)
                  }  in
                let e2 =
                  let uu___1098_71624 = e1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1098_71624.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1098_71624.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1098_71624.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1098_71624.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1098_71624.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1098_71624.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1098_71624.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1098_71624.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1098_71624.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1098_71624.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1098_71624.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1098_71624.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1098_71624.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1098_71624.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1098_71624.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1098_71624.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1098_71624.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1098_71624.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1098_71624.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1098_71624.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1098_71624.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1098_71624.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1098_71624.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1098_71624.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___1098_71624.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1098_71624.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1098_71624.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1098_71624.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1098_71624.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1098_71624.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1098_71624.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1098_71624.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1098_71624.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1098_71624.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1098_71624.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1098_71624.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1098_71624.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1098_71624.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1098_71624.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1098_71624.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1098_71624.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1098_71624.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___1102_71639  ->
                     match () with
                     | () ->
                         let uu____71648 =
                           FStar_TypeChecker_TcTerm.tc_term e2 t  in
                         (match uu____71648 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____71686,msg) ->
                    let uu____71690 = tts e2 t  in
                    let uu____71692 =
                      let uu____71694 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____71694
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____71690 uu____71692 msg
                | FStar_Errors.Error (uu____71704,msg,uu____71706) ->
                    let uu____71709 = tts e2 t  in
                    let uu____71711 =
                      let uu____71713 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____71713
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____71709 uu____71711 msg))
  
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
  fun uu____71747  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___1127_71766 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___1127_71766.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___1127_71766.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___1127_71766.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___1127_71766.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___1127_71766.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___1127_71766.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___1127_71766.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___1127_71766.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___1127_71766.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___1127_71766.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___1127_71766.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___1127_71766.FStar_Tactics_Types.local_state)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____71791 = get_guard_policy ()  in
      bind uu____71791
        (fun old_pol  ->
           let uu____71797 = set_guard_policy pol  in
           bind uu____71797
             (fun uu____71801  ->
                bind t
                  (fun r  ->
                     let uu____71805 = set_guard_policy old_pol  in
                     bind uu____71805 (fun uu____71809  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____71813 = let uu____71818 = cur_goal ()  in trytac uu____71818  in
  bind uu____71813
    (fun uu___609_71825  ->
       match uu___609_71825 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____71831 = FStar_Options.peek ()  in ret uu____71831)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        mlog
          (fun uu____71856  ->
             let uu____71857 = FStar_TypeChecker_Rel.guard_to_string e g  in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason
               uu____71857)
          (fun uu____71862  ->
             let uu____71863 =
               add_implicits g.FStar_TypeChecker_Env.implicits  in
             bind uu____71863
               (fun uu____71867  ->
                  bind getopts
                    (fun opts  ->
                       let uu____71871 =
                         let uu____71872 =
                           FStar_TypeChecker_Rel.simplify_guard e g  in
                         uu____71872.FStar_TypeChecker_Env.guard_f  in
                       match uu____71871 with
                       | FStar_TypeChecker_Common.Trivial  -> ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____71876 = istrivial e f  in
                           if uu____71876
                           then ret ()
                           else
                             bind get
                               (fun ps  ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop  ->
                                      ((let uu____71889 =
                                          let uu____71895 =
                                            let uu____71897 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g
                                               in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____71897
                                             in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____71895)
                                           in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____71889);
                                       ret ())
                                  | FStar_Tactics_Types.Goal  ->
                                      mlog
                                        (fun uu____71903  ->
                                           let uu____71904 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____71904)
                                        (fun uu____71909  ->
                                           let uu____71910 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____71910
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___1156_71918 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___1156_71918.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___1156_71918.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___1156_71918.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___1156_71918.FStar_Tactics_Types.label)
                                                  }  in
                                                push_goals [goal1]))
                                  | FStar_Tactics_Types.SMT  ->
                                      mlog
                                        (fun uu____71922  ->
                                           let uu____71923 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____71923)
                                        (fun uu____71928  ->
                                           let uu____71929 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____71929
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___1163_71937 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___1163_71937.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___1163_71937.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___1163_71937.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___1163_71937.FStar_Tactics_Types.label)
                                                  }  in
                                                push_smt_goals [goal1]))
                                  | FStar_Tactics_Types.Force  ->
                                      mlog
                                        (fun uu____71941  ->
                                           let uu____71942 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____71942)
                                        (fun uu____71946  ->
                                           try
                                             (fun uu___1170_71951  ->
                                                match () with
                                                | () ->
                                                    let uu____71954 =
                                                      let uu____71956 =
                                                        let uu____71958 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____71958
                                                         in
                                                      Prims.op_Negation
                                                        uu____71956
                                                       in
                                                    if uu____71954
                                                    then
                                                      mlog
                                                        (fun uu____71965  ->
                                                           let uu____71966 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g
                                                              in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____71966)
                                                        (fun uu____71970  ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else ret ()) ()
                                           with
                                           | uu___1169_71975 ->
                                               mlog
                                                 (fun uu____71980  ->
                                                    let uu____71981 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g
                                                       in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____71981)
                                                 (fun uu____71985  ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____71997 =
      let uu____72000 = cur_goal ()  in
      bind uu____72000
        (fun goal  ->
           let uu____72006 =
             let uu____72015 = FStar_Tactics_Types.goal_env goal  in
             __tc_lax uu____72015 t  in
           bind uu____72006
             (fun uu____72026  ->
                match uu____72026 with
                | (uu____72035,typ,uu____72037) -> ret typ))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____71997
  
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
            let uu____72077 = mk_irrelevant_goal reason env phi opts label1
               in
            bind uu____72077 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____72089  ->
    let uu____72092 = cur_goal ()  in
    bind uu____72092
      (fun goal  ->
         let uu____72098 =
           let uu____72100 = FStar_Tactics_Types.goal_env goal  in
           let uu____72101 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____72100 uu____72101  in
         if uu____72098
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____72107 =
              let uu____72109 = FStar_Tactics_Types.goal_env goal  in
              let uu____72110 = FStar_Tactics_Types.goal_type goal  in
              tts uu____72109 uu____72110  in
            fail1 "Not a trivial goal: %s" uu____72107))
  
let divide : 'a 'b . FStar_BigInt.t -> 'a tac -> 'b tac -> ('a * 'b) tac =
  fun n1  ->
    fun l  ->
      fun r  ->
        bind get
          (fun p  ->
             let uu____72161 =
               try
                 (fun uu___1226_72184  ->
                    match () with
                    | () ->
                        let uu____72195 =
                          let uu____72204 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____72204
                            p.FStar_Tactics_Types.goals
                           in
                        ret uu____72195) ()
               with | uu___1225_72215 -> fail "divide: not enough goals"  in
             bind uu____72161
               (fun uu____72252  ->
                  match uu____72252 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___1208_72278 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___1208_72278.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___1208_72278.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___1208_72278.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___1208_72278.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___1208_72278.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___1208_72278.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___1208_72278.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___1208_72278.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___1208_72278.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___1208_72278.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___1208_72278.FStar_Tactics_Types.local_state)
                        }  in
                      let uu____72279 = set lp  in
                      bind uu____72279
                        (fun uu____72287  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___1214_72303 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___1214_72303.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___1214_72303.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___1214_72303.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___1214_72303.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___1214_72303.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___1214_72303.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___1214_72303.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___1214_72303.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___1214_72303.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___1214_72303.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___1214_72303.FStar_Tactics_Types.local_state)
                                       }  in
                                     let uu____72304 = set rp  in
                                     bind uu____72304
                                       (fun uu____72312  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___1220_72328 =
                                                        rp'  in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___1220_72328.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___1220_72328.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___1220_72328.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___1220_72328.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___1220_72328.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___1220_72328.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___1220_72328.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___1220_72328.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___1220_72328.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___1220_72328.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___1220_72328.FStar_Tactics_Types.local_state)
                                                      }  in
                                                    let uu____72329 = set p'
                                                       in
                                                    bind uu____72329
                                                      (fun uu____72337  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____72343 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____72365 = divide FStar_BigInt.one f idtac  in
    bind uu____72365
      (fun uu____72378  -> match uu____72378 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____72416::uu____72417 ->
             let uu____72420 =
               let uu____72429 = map tau  in
               divide FStar_BigInt.one tau uu____72429  in
             bind uu____72420
               (fun uu____72447  ->
                  match uu____72447 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____72489 =
        bind t1
          (fun uu____72494  ->
             let uu____72495 = map t2  in
             bind uu____72495 (fun uu____72503  -> ret ()))
         in
      focus uu____72489
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____72513  ->
    let uu____72516 =
      let uu____72519 = cur_goal ()  in
      bind uu____72519
        (fun goal  ->
           let uu____72528 =
             let uu____72535 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____72535  in
           match uu____72528 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____72544 =
                 let uu____72546 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____72546  in
               if uu____72544
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____72555 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____72555 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____72569 = new_uvar "intro" env' typ'  in
                  bind uu____72569
                    (fun uu____72586  ->
                       match uu____72586 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c))
                              in
                           let uu____72610 = set_solution goal sol  in
                           bind uu____72610
                             (fun uu____72616  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                    goal.FStar_Tactics_Types.label
                                   in
                                let uu____72618 =
                                  let uu____72621 = bnorm_goal g  in
                                  replace_cur uu____72621  in
                                bind uu____72618 (fun uu____72623  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____72628 =
                 let uu____72630 = FStar_Tactics_Types.goal_env goal  in
                 let uu____72631 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____72630 uu____72631  in
               fail1 "goal is not an arrow (%s)" uu____72628)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____72516
  
let (intro_rec :
  unit -> (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder) tac) =
  fun uu____72649  ->
    let uu____72656 = cur_goal ()  in
    bind uu____72656
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____72675 =
            let uu____72682 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____72682  in
          match uu____72675 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____72695 =
                let uu____72697 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____72697  in
              if uu____72695
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____72714 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____72714
                    in
                 let bs =
                   let uu____72725 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____72725; b]  in
                 let env' =
                   let uu____72751 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____72751 bs  in
                 let uu____72752 =
                   let uu____72759 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____72759  in
                 bind uu____72752
                   (fun uu____72779  ->
                      match uu____72779 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____72793 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____72796 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____72793
                              FStar_Parser_Const.effect_Tot_lid uu____72796
                              [] FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____72814 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____72814 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____72836 =
                                   let uu____72837 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____72837.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____72836
                                  in
                               let uu____72853 = set_solution goal tm  in
                               bind uu____72853
                                 (fun uu____72862  ->
                                    let uu____72863 =
                                      let uu____72866 =
                                        bnorm_goal
                                          (let uu___1291_72869 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___1291_72869.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___1291_72869.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___1291_72869.FStar_Tactics_Types.is_guard);
                                             FStar_Tactics_Types.label =
                                               (uu___1291_72869.FStar_Tactics_Types.label)
                                           })
                                         in
                                      replace_cur uu____72866  in
                                    bind uu____72863
                                      (fun uu____72876  ->
                                         let uu____72877 =
                                           let uu____72882 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____72882, b)  in
                                         ret uu____72877)))))
          | FStar_Pervasives_Native.None  ->
              let uu____72891 =
                let uu____72893 = FStar_Tactics_Types.goal_env goal  in
                let uu____72894 = FStar_Tactics_Types.goal_type goal  in
                tts uu____72893 uu____72894  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____72891))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____72914 = cur_goal ()  in
    bind uu____72914
      (fun goal  ->
         mlog
           (fun uu____72921  ->
              let uu____72922 =
                let uu____72924 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____72924  in
              FStar_Util.print1 "norm: witness = %s\n" uu____72922)
           (fun uu____72930  ->
              let steps =
                let uu____72934 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____72934
                 in
              let t =
                let uu____72938 = FStar_Tactics_Types.goal_env goal  in
                let uu____72939 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____72938 uu____72939  in
              let uu____72940 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____72940))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____72965 =
          bind get
            (fun ps  ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
                 | g::uu____72973 -> g.FStar_Tactics_Types.opts
                 | uu____72976 -> FStar_Options.peek ()  in
               mlog
                 (fun uu____72981  ->
                    let uu____72982 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____72982)
                 (fun uu____72987  ->
                    let uu____72988 = __tc_lax e t  in
                    bind uu____72988
                      (fun uu____73009  ->
                         match uu____73009 with
                         | (t1,uu____73019,uu____73020) ->
                             let steps =
                               let uu____73024 =
                                 FStar_TypeChecker_Normalize.tr_norm_steps s
                                  in
                               FStar_List.append
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu____73024
                                in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1
                                in
                             mlog
                               (fun uu____73030  ->
                                  let uu____73031 =
                                    FStar_Syntax_Print.term_to_string t2  in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____73031)
                               (fun uu____73035  -> ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____72965
  
let (refine_intro : unit -> unit tac) =
  fun uu____73048  ->
    let uu____73051 =
      let uu____73054 = cur_goal ()  in
      bind uu____73054
        (fun g  ->
           let uu____73061 =
             let uu____73072 = FStar_Tactics_Types.goal_env g  in
             let uu____73073 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____73072
               uu____73073
              in
           match uu____73061 with
           | (uu____73076,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____73102 =
                 let uu____73107 =
                   let uu____73112 =
                     let uu____73113 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____73113]  in
                   FStar_Syntax_Subst.open_term uu____73112 phi  in
                 match uu____73107 with
                 | (bvs,phi1) ->
                     let uu____73138 =
                       let uu____73139 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____73139  in
                     (uu____73138, phi1)
                  in
               (match uu____73102 with
                | (bv1,phi1) ->
                    let uu____73158 =
                      let uu____73161 = FStar_Tactics_Types.goal_env g  in
                      let uu____73162 =
                        let uu____73163 =
                          let uu____73166 =
                            let uu____73167 =
                              let uu____73174 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____73174)  in
                            FStar_Syntax_Syntax.NT uu____73167  in
                          [uu____73166]  in
                        FStar_Syntax_Subst.subst uu____73163 phi1  in
                      mk_irrelevant_goal "refine_intro refinement"
                        uu____73161 uu____73162 g.FStar_Tactics_Types.opts
                        g.FStar_Tactics_Types.label
                       in
                    bind uu____73158
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____73183  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____73051
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____73206 = cur_goal ()  in
      bind uu____73206
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____73215 = FStar_Tactics_Types.goal_env goal  in
               let uu____73216 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____73215 uu____73216
             else FStar_Tactics_Types.goal_env goal  in
           let uu____73219 = __tc env t  in
           bind uu____73219
             (fun uu____73238  ->
                match uu____73238 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____73253  ->
                         let uu____73254 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____73256 =
                           let uu____73258 =
                             FStar_Tactics_Types.goal_env goal  in
                           FStar_TypeChecker_Rel.guard_to_string uu____73258
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____73254 uu____73256)
                      (fun uu____73262  ->
                         let uu____73263 =
                           let uu____73266 =
                             FStar_Tactics_Types.goal_env goal  in
                           proc_guard "__exact typing" uu____73266 guard  in
                         bind uu____73263
                           (fun uu____73269  ->
                              mlog
                                (fun uu____73273  ->
                                   let uu____73274 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____73276 =
                                     let uu____73278 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____73278
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____73274 uu____73276)
                                (fun uu____73282  ->
                                   let uu____73283 =
                                     let uu____73287 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____73288 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____73287 typ uu____73288  in
                                   bind uu____73283
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____73298 =
                                             let uu____73300 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____73300 t1  in
                                           let uu____73301 =
                                             let uu____73303 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____73303 typ  in
                                           let uu____73304 =
                                             let uu____73306 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____73307 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____73306 uu____73307  in
                                           let uu____73308 =
                                             let uu____73310 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____73311 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____73310 uu____73311  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____73298 uu____73301
                                             uu____73304 uu____73308)))))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun try_refine  ->
    fun set_expected_typ1  ->
      fun tm  ->
        let uu____73337 =
          mlog
            (fun uu____73342  ->
               let uu____73343 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____73343)
            (fun uu____73348  ->
               let uu____73349 =
                 let uu____73356 = __exact_now set_expected_typ1 tm  in
                 catch uu____73356  in
               bind uu____73349
                 (fun uu___611_73365  ->
                    match uu___611_73365 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        traise e
                    | FStar_Util.Inl e ->
                        mlog
                          (fun uu____73376  ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____73380  ->
                             let uu____73381 =
                               let uu____73388 =
                                 let uu____73391 =
                                   norm [FStar_Syntax_Embeddings.Delta]  in
                                 bind uu____73391
                                   (fun uu____73396  ->
                                      let uu____73397 = refine_intro ()  in
                                      bind uu____73397
                                        (fun uu____73401  ->
                                           __exact_now set_expected_typ1 tm))
                                  in
                               catch uu____73388  in
                             bind uu____73381
                               (fun uu___610_73408  ->
                                  match uu___610_73408 with
                                  | FStar_Util.Inr r ->
                                      mlog
                                        (fun uu____73417  ->
                                           FStar_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu____73420  -> ret ())
                                  | FStar_Util.Inl uu____73421 ->
                                      mlog
                                        (fun uu____73423  ->
                                           FStar_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu____73426  -> traise e)))))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____73337
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____73478 = f x  in
          bind uu____73478
            (fun y  ->
               let uu____73486 = mapM f xs  in
               bind uu____73486 (fun ys  -> ret (y :: ys)))
  
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
          let uu____73558 = do_unify e ty1 ty2  in
          bind uu____73558
            (fun uu___612_73572  ->
               if uu___612_73572
               then ret acc
               else
                 (let uu____73592 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____73592 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____73613 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____73615 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____73613
                        uu____73615
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____73632 =
                        let uu____73634 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____73634  in
                      if uu____73632
                      then fail "Codomain is effectful"
                      else
                        (let uu____73658 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____73658
                           (fun uu____73685  ->
                              match uu____73685 with
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
      let uu____73775 =
        mlog
          (fun uu____73780  ->
             let uu____73781 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_apply: tm = %s\n" uu____73781)
          (fun uu____73786  ->
             let uu____73787 = cur_goal ()  in
             bind uu____73787
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____73795 = __tc e tm  in
                  bind uu____73795
                    (fun uu____73816  ->
                       match uu____73816 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____73829 =
                             let uu____73840 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____73840  in
                           bind uu____73829
                             (fun uvs  ->
                                let fix_qual q =
                                  match q with
                                  | FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Meta uu____73878)
                                      ->
                                      FStar_Pervasives_Native.Some
                                        (FStar_Syntax_Syntax.Implicit false)
                                  | uu____73882 -> q  in
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____73905  ->
                                       fun w  ->
                                         match uu____73905 with
                                         | (uvt,q,uu____73923) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, (fix_qual q))]) uvs tm1
                                   in
                                let uvset =
                                  let uu____73955 =
                                    FStar_Syntax_Free.new_uv_set ()  in
                                  FStar_List.fold_right
                                    (fun uu____73972  ->
                                       fun s  ->
                                         match uu____73972 with
                                         | (uu____73984,uu____73985,uv) ->
                                             let uu____73987 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                in
                                             FStar_Util.set_union s
                                               uu____73987) uvs uu____73955
                                   in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset  in
                                let uu____73997 = solve' goal w  in
                                bind uu____73997
                                  (fun uu____74002  ->
                                     let uu____74003 =
                                       mapM
                                         (fun uu____74020  ->
                                            match uu____74020 with
                                            | (uvt,q,uv) ->
                                                let uu____74032 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                   in
                                                (match uu____74032 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____74037 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____74038 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv)
                                                        in
                                                     if uu____74038
                                                     then ret ()
                                                     else
                                                       (let uu____74045 =
                                                          let uu____74048 =
                                                            bnorm_goal
                                                              (let uu___1452_74051
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___1452_74051.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___1452_74051.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false;
                                                                 FStar_Tactics_Types.label
                                                                   =
                                                                   (uu___1452_74051.FStar_Tactics_Types.label)
                                                               })
                                                             in
                                                          [uu____74048]  in
                                                        add_goals uu____74045)))
                                         uvs
                                        in
                                     bind uu____74003
                                       (fun uu____74056  ->
                                          proc_guard "apply guard" e guard))))))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____73775
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____74084 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____74084
    then
      let uu____74093 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____74108 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____74161 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____74093 with
      | (pre,post) ->
          let post1 =
            let uu____74194 =
              let uu____74205 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____74205]  in
            FStar_Syntax_Util.mk_app post uu____74194  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____74236 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____74236
       then
         let uu____74245 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____74245
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
            let uu____74324 = f x e  in
            bind uu____74324 (fun e'  -> fold_left f e' xs1)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____74339 =
      let uu____74342 =
        bind get
          (fun ps  ->
             mlog
               (fun uu____74349  ->
                  let uu____74350 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____74350)
               (fun uu____74356  ->
                  let is_unit_t t =
                    let uu____74364 =
                      let uu____74365 = FStar_Syntax_Subst.compress t  in
                      uu____74365.FStar_Syntax_Syntax.n  in
                    match uu____74364 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____74371 -> false  in
                  let uu____74373 = cur_goal ()  in
                  bind uu____74373
                    (fun goal  ->
                       let uu____74379 =
                         let uu____74388 = FStar_Tactics_Types.goal_env goal
                            in
                         __tc uu____74388 tm  in
                       bind uu____74379
                         (fun uu____74403  ->
                            match uu____74403 with
                            | (tm1,t,guard) ->
                                let uu____74415 =
                                  FStar_Syntax_Util.arrow_formals_comp t  in
                                (match uu____74415 with
                                 | (bs,comp) ->
                                     let uu____74448 = lemma_or_sq comp  in
                                     (match uu____74448 with
                                      | FStar_Pervasives_Native.None  ->
                                          fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre,post) ->
                                          let uu____74468 =
                                            fold_left
                                              (fun uu____74530  ->
                                                 fun uu____74531  ->
                                                   match (uu____74530,
                                                           uu____74531)
                                                   with
                                                   | ((b,aq),(uvs,imps,subst1))
                                                       ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst1
                                                           b.FStar_Syntax_Syntax.sort
                                                          in
                                                       let uu____74682 =
                                                         is_unit_t b_t  in
                                                       if uu____74682
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
                                                         (let uu____74805 =
                                                            let uu____74812 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            new_uvar
                                                              "apply_lemma"
                                                              uu____74812 b_t
                                                             in
                                                          bind uu____74805
                                                            (fun uu____74843 
                                                               ->
                                                               match uu____74843
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
                                          bind uu____74468
                                            (fun uu____75029  ->
                                               match uu____75029 with
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
                                                   let uu____75117 =
                                                     let uu____75121 =
                                                       FStar_Tactics_Types.goal_env
                                                         goal
                                                        in
                                                     let uu____75122 =
                                                       FStar_Syntax_Util.mk_squash
                                                         FStar_Syntax_Syntax.U_zero
                                                         post1
                                                        in
                                                     let uu____75123 =
                                                       FStar_Tactics_Types.goal_type
                                                         goal
                                                        in
                                                     do_unify uu____75121
                                                       uu____75122
                                                       uu____75123
                                                      in
                                                   bind uu____75117
                                                     (fun b  ->
                                                        if
                                                          Prims.op_Negation b
                                                        then
                                                          let uu____75134 =
                                                            let uu____75136 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            tts uu____75136
                                                              tm1
                                                             in
                                                          let uu____75137 =
                                                            let uu____75139 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            let uu____75140 =
                                                              FStar_Syntax_Util.mk_squash
                                                                FStar_Syntax_Syntax.U_zero
                                                                post1
                                                               in
                                                            tts uu____75139
                                                              uu____75140
                                                             in
                                                          let uu____75141 =
                                                            let uu____75143 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            let uu____75144 =
                                                              FStar_Tactics_Types.goal_type
                                                                goal
                                                               in
                                                            tts uu____75143
                                                              uu____75144
                                                             in
                                                          fail3
                                                            "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                            uu____75134
                                                            uu____75137
                                                            uu____75141
                                                        else
                                                          (let uu____75148 =
                                                             solve' goal
                                                               FStar_Syntax_Util.exp_unit
                                                              in
                                                           bind uu____75148
                                                             (fun uu____75156
                                                                 ->
                                                                let is_free_uvar
                                                                  uv t1 =
                                                                  let free_uvars
                                                                    =
                                                                    let uu____75182
                                                                    =
                                                                    let uu____75185
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____75185
                                                                     in
                                                                    FStar_List.map
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____75182
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
                                                                    let uu____75221
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____75221)
                                                                    goals
                                                                   in
                                                                let checkone
                                                                  t1 goals =
                                                                  let uu____75238
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                  match uu____75238
                                                                  with
                                                                  | (hd1,uu____75257)
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____75284)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____75301
                                                                    -> false)
                                                                   in
                                                                let uu____75303
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
                                                                    let uu____75346
                                                                    = imp  in
                                                                    match uu____75346
                                                                    with
                                                                    | 
                                                                    (term,ctx_uvar)
                                                                    ->
                                                                    let uu____75357
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____75357
                                                                    with
                                                                    | 
                                                                    (hd1,uu____75379)
                                                                    ->
                                                                    let uu____75404
                                                                    =
                                                                    let uu____75405
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____75405.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____75404
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____75413)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___1562_75433
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___1562_75433.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___1562_75433.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___1562_75433.FStar_Tactics_Types.is_guard);
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___1562_75433.FStar_Tactics_Types.label)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____75436
                                                                    ->
                                                                    mlog
                                                                    (fun
                                                                    uu____75442
                                                                     ->
                                                                    let uu____75443
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                                                     in
                                                                    let uu____75445
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____75443
                                                                    uu____75445)
                                                                    (fun
                                                                    uu____75452
                                                                     ->
                                                                    let env =
                                                                    let uu___1567_75454
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___1567_75454.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1567_75454.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1567_75454.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___1567_75454.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1567_75454.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1567_75454.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1567_75454.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1567_75454.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___1567_75454.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___1567_75454.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___1567_75454.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1567_75454.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1567_75454.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1567_75454.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1567_75454.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1567_75454.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1567_75454.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1567_75454.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___1567_75454.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___1567_75454.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___1567_75454.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1567_75454.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1567_75454.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1567_75454.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1567_75454.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1567_75454.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1567_75454.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1567_75454.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1567_75454.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1567_75454.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1567_75454.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1567_75454.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1567_75454.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1567_75454.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___1567_75454.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1567_75454.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1567_75454.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___1567_75454.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1567_75454.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1567_75454.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1567_75454.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1567_75454.FStar_TypeChecker_Env.nbe)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let uu____75457
                                                                    =
                                                                    let uu____75460
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____75464
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
                                                                    let uu____75466
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____75464
                                                                    uu____75466
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____75472
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    uu____75460
                                                                    uu____75472
                                                                    g_typ  in
                                                                    bind
                                                                    uu____75457
                                                                    (fun
                                                                    uu____75476
                                                                     ->
                                                                    ret []))))))
                                                                   in
                                                                bind
                                                                  uu____75303
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
                                                                    let uu____75540
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____75540
                                                                    then
                                                                    let uu____75545
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____75545
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
                                                                    let uu____75560
                                                                    =
                                                                    let uu____75562
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____75562
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____75560)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____75563
                                                                    =
                                                                    let uu____75566
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____75566
                                                                    guard  in
                                                                    bind
                                                                    uu____75563
                                                                    (fun
                                                                    uu____75570
                                                                     ->
                                                                    let uu____75571
                                                                    =
                                                                    let uu____75574
                                                                    =
                                                                    let uu____75576
                                                                    =
                                                                    let uu____75578
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____75579
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____75578
                                                                    uu____75579
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____75576
                                                                     in
                                                                    if
                                                                    uu____75574
                                                                    then
                                                                    let uu____75583
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____75583
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    goal.FStar_Tactics_Types.label
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____75571
                                                                    (fun
                                                                    uu____75588
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2)))))))))))))
         in
      focus uu____74342  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____74339
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____75612 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____75612 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____75622::(e1,uu____75624)::(e2,uu____75626)::[])) when
        (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) ||
          (FStar_Ident.lid_equals l FStar_Parser_Const.c_eq2_lid)
        -> FStar_Pervasives_Native.Some (e1, e2)
    | uu____75687 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____75712 = destruct_eq' typ  in
    match uu____75712 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____75742 = FStar_Syntax_Util.un_squash typ  in
        (match uu____75742 with
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
        let uu____75811 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____75811 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', bv', [])
            else
              (let uu____75869 = aux e'  in
               FStar_Util.map_opt uu____75869
                 (fun uu____75900  ->
                    match uu____75900 with
                    | (e'',bv,bvs) -> (e'', bv, (bv' :: bvs))))
         in
      let uu____75926 = aux e  in
      FStar_Util.map_opt uu____75926
        (fun uu____75957  ->
           match uu____75957 with
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
          let uu____76031 =
            let uu____76042 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____76042  in
          FStar_Util.map_opt uu____76031
            (fun uu____76060  ->
               match uu____76060 with
               | (e0,b11,bvs) ->
                   let s1 bv =
                     let uu___1640_76082 = bv  in
                     let uu____76083 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___1640_76082.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___1640_76082.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____76083
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___1644_76091 =
                       g.FStar_Tactics_Types.goal_ctx_uvar  in
                     let uu____76092 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____76101 =
                       let uu____76104 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____76104  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___1644_76091.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____76092;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____76101;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___1644_76091.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___1644_76091.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___1644_76091.FStar_Syntax_Syntax.ctx_uvar_range);
                       FStar_Syntax_Syntax.ctx_uvar_meta =
                         (uu___1644_76091.FStar_Syntax_Syntax.ctx_uvar_meta)
                     }  in
                   let uu___1647_76105 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1647_76105.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___1647_76105.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___1647_76105.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1647_76105.FStar_Tactics_Types.label)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____76116 =
      let uu____76119 = cur_goal ()  in
      bind uu____76119
        (fun goal  ->
           let uu____76127 = h  in
           match uu____76127 with
           | (bv,uu____76131) ->
               mlog
                 (fun uu____76139  ->
                    let uu____76140 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____76142 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____76140
                      uu____76142)
                 (fun uu____76147  ->
                    let uu____76148 =
                      let uu____76159 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____76159  in
                    match uu____76148 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                        let uu____76186 =
                          destruct_eq bv1.FStar_Syntax_Syntax.sort  in
                        (match uu____76186 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____76201 =
                               let uu____76202 =
                                 FStar_Syntax_Subst.compress x  in
                               uu____76202.FStar_Syntax_Syntax.n  in
                             (match uu____76201 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv2 =
                                    let uu___1670_76219 = bv2  in
                                    let uu____76220 =
                                      FStar_Syntax_Subst.subst s
                                        bv2.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1670_76219.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1670_76219.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____76220
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv1 :: bvs1)  in
                                  let new_goal =
                                    let uu___1674_76228 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____76229 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____76238 =
                                      let uu____76241 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____76241
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___1674_76228.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____76229;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____76238;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___1674_76228.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___1674_76228.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___1674_76228.FStar_Syntax_Syntax.ctx_uvar_range);
                                      FStar_Syntax_Syntax.ctx_uvar_meta =
                                        (uu___1674_76228.FStar_Syntax_Syntax.ctx_uvar_meta)
                                    }  in
                                  replace_cur
                                    (let uu___1677_76244 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___1677_76244.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___1677_76244.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___1677_76244.FStar_Tactics_Types.is_guard);
                                       FStar_Tactics_Types.label =
                                         (uu___1677_76244.FStar_Tactics_Types.label)
                                     })
                              | uu____76245 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____76247 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____76116
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____76277 =
        let uu____76280 = cur_goal ()  in
        bind uu____76280
          (fun goal  ->
             let uu____76291 = b  in
             match uu____76291 with
             | (bv,uu____76295) ->
                 let bv' =
                   let uu____76301 =
                     let uu___1688_76302 = bv  in
                     let uu____76303 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____76303;
                       FStar_Syntax_Syntax.index =
                         (uu___1688_76302.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___1688_76302.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____76301  in
                 let s1 =
                   let uu____76308 =
                     let uu____76309 =
                       let uu____76316 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____76316)  in
                     FStar_Syntax_Syntax.NT uu____76309  in
                   [uu____76308]  in
                 let uu____76321 = subst_goal bv bv' s1 goal  in
                 (match uu____76321 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____76277
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____76343 =
      let uu____76346 = cur_goal ()  in
      bind uu____76346
        (fun goal  ->
           let uu____76355 = b  in
           match uu____76355 with
           | (bv,uu____76359) ->
               let uu____76364 =
                 let uu____76375 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____76375  in
               (match uu____76364 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                    let uu____76402 = FStar_Syntax_Util.type_u ()  in
                    (match uu____76402 with
                     | (ty,u) ->
                         let uu____76411 = new_uvar "binder_retype" e0 ty  in
                         bind uu____76411
                           (fun uu____76430  ->
                              match uu____76430 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___1712_76440 = bv1  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1712_76440.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1712_76440.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____76444 =
                                      let uu____76445 =
                                        let uu____76452 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv1, uu____76452)  in
                                      FStar_Syntax_Syntax.NT uu____76445  in
                                    [uu____76444]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___1717_76464 = b1  in
                                         let uu____76465 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___1717_76464.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___1717_76464.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____76465
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____76472  ->
                                       let new_goal =
                                         let uu____76474 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____76475 =
                                           let uu____76476 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____76476
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____76474 uu____76475
                                          in
                                       let uu____76477 = add_goals [new_goal]
                                          in
                                       bind uu____76477
                                         (fun uu____76482  ->
                                            let uu____76483 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv1.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____76483
                                              goal.FStar_Tactics_Types.opts
                                              goal.FStar_Tactics_Types.label))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____76343
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____76509 =
        let uu____76512 = cur_goal ()  in
        bind uu____76512
          (fun goal  ->
             let uu____76521 = b  in
             match uu____76521 with
             | (bv,uu____76525) ->
                 let uu____76530 =
                   let uu____76541 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____76541  in
                 (match uu____76530 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                      let steps =
                        let uu____76571 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____76571
                         in
                      let sort' =
                        normalize steps e0 bv1.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___1738_76576 = bv1  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___1738_76576.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___1738_76576.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____76578 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____76578))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____76509
  
let (revert : unit -> unit tac) =
  fun uu____76591  ->
    let uu____76594 = cur_goal ()  in
    bind uu____76594
      (fun goal  ->
         let uu____76600 =
           let uu____76607 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____76607  in
         match uu____76600 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____76624 =
                 let uu____76627 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____76627  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____76624
                in
             let uu____76642 = new_uvar "revert" env' typ'  in
             bind uu____76642
               (fun uu____76658  ->
                  match uu____76658 with
                  | (r,u_r) ->
                      let uu____76667 =
                        let uu____76670 =
                          let uu____76671 =
                            let uu____76672 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____76672.FStar_Syntax_Syntax.pos  in
                          let uu____76675 =
                            let uu____76680 =
                              let uu____76681 =
                                let uu____76690 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____76690  in
                              [uu____76681]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____76680  in
                          uu____76675 FStar_Pervasives_Native.None
                            uu____76671
                           in
                        set_solution goal uu____76670  in
                      bind uu____76667
                        (fun uu____76711  ->
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
      let uu____76725 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____76725
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____76741 = cur_goal ()  in
    bind uu____76741
      (fun goal  ->
         mlog
           (fun uu____76749  ->
              let uu____76750 = FStar_Syntax_Print.binder_to_string b  in
              let uu____76752 =
                let uu____76754 =
                  let uu____76756 =
                    let uu____76765 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____76765  in
                  FStar_All.pipe_right uu____76756 FStar_List.length  in
                FStar_All.pipe_right uu____76754 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____76750 uu____76752)
           (fun uu____76786  ->
              let uu____76787 =
                let uu____76798 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____76798  in
              match uu____76787 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bv1,bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____76843 =
                          free_in bv1 bv'.FStar_Syntax_Syntax.sort  in
                        if uu____76843
                        then
                          let uu____76848 =
                            let uu____76850 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____76850
                             in
                          fail uu____76848
                        else check1 bvs2
                     in
                  let uu____76855 =
                    let uu____76857 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv1 uu____76857  in
                  if uu____76855
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____76864 = check1 bvs  in
                     bind uu____76864
                       (fun uu____76870  ->
                          let env' = push_bvs e' bvs  in
                          let uu____76872 =
                            let uu____76879 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____76879  in
                          bind uu____76872
                            (fun uu____76889  ->
                               match uu____76889 with
                               | (ut,uvar_ut) ->
                                   let uu____76898 = set_solution goal ut  in
                                   bind uu____76898
                                     (fun uu____76903  ->
                                        let uu____76904 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                            goal.FStar_Tactics_Types.label
                                           in
                                        replace_cur uu____76904))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____76912  ->
    let uu____76915 = cur_goal ()  in
    bind uu____76915
      (fun goal  ->
         let uu____76921 =
           let uu____76928 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____76928  in
         match uu____76921 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____76937) ->
             let uu____76942 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____76942)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____76955 = cur_goal ()  in
    bind uu____76955
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____76965 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____76965  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____76968  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____76981 = cur_goal ()  in
    bind uu____76981
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____76991 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____76991  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____76994  -> add_goals [g']))
  
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
            let uu____77035 = FStar_Syntax_Subst.compress t  in
            uu____77035.FStar_Syntax_Syntax.n  in
          let uu____77038 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___1922_77045 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___1922_77045.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___1922_77045.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____77038
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____77062 =
                   let uu____77063 = FStar_Syntax_Subst.compress t1  in
                   uu____77063.FStar_Syntax_Syntax.n  in
                 match uu____77062 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____77094 = ff hd1  in
                     bind uu____77094
                       (fun hd2  ->
                          let fa uu____77120 =
                            match uu____77120 with
                            | (a,q) ->
                                let uu____77141 = ff a  in
                                bind uu____77141 (fun a1  -> ret (a1, q))
                             in
                          let uu____77160 = mapM fa args  in
                          bind uu____77160
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____77242 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____77242 with
                      | (bs1,t') ->
                          let uu____77251 =
                            let uu____77254 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____77254 t'  in
                          bind uu____77251
                            (fun t''  ->
                               let uu____77258 =
                                 let uu____77259 =
                                   let uu____77278 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____77287 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____77278, uu____77287, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____77259  in
                               ret uu____77258))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____77362 = ff hd1  in
                     bind uu____77362
                       (fun hd2  ->
                          let ffb br =
                            let uu____77377 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____77377 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____77409 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____77409  in
                                let uu____77410 = ff1 e  in
                                bind uu____77410
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____77425 = mapM ffb brs  in
                          bind uu____77425
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____77469;
                          FStar_Syntax_Syntax.lbtyp = uu____77470;
                          FStar_Syntax_Syntax.lbeff = uu____77471;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____77473;
                          FStar_Syntax_Syntax.lbpos = uu____77474;_}::[]),e)
                     ->
                     let lb =
                       let uu____77502 =
                         let uu____77503 = FStar_Syntax_Subst.compress t1  in
                         uu____77503.FStar_Syntax_Syntax.n  in
                       match uu____77502 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____77507) -> lb
                       | uu____77523 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____77533 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____77533
                         (fun def1  ->
                            ret
                              (let uu___1875_77539 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1875_77539.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1875_77539.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1875_77539.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1875_77539.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1875_77539.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1875_77539.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____77540 = fflb lb  in
                     bind uu____77540
                       (fun lb1  ->
                          let uu____77550 =
                            let uu____77555 =
                              let uu____77556 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____77556]  in
                            FStar_Syntax_Subst.open_term uu____77555 e  in
                          match uu____77550 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____77586 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____77586  in
                              let uu____77587 = ff1 e1  in
                              bind uu____77587
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____77634 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____77634
                         (fun def  ->
                            ret
                              (let uu___1893_77640 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1893_77640.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1893_77640.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1893_77640.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1893_77640.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1893_77640.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1893_77640.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____77641 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____77641 with
                      | (lbs1,e1) ->
                          let uu____77656 = mapM fflb lbs1  in
                          bind uu____77656
                            (fun lbs2  ->
                               let uu____77668 = ff e1  in
                               bind uu____77668
                                 (fun e2  ->
                                    let uu____77676 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____77676 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____77747 = ff t2  in
                     bind uu____77747
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____77778 = ff t2  in
                     bind uu____77778
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____77785 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___1917_77792 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___1917_77792.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___1917_77792.FStar_Syntax_Syntax.vars)
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
              let uu____77839 =
                FStar_TypeChecker_TcTerm.tc_term
                  (let uu___1930_77848 = env  in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___1930_77848.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___1930_77848.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___1930_77848.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___1930_77848.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_sig =
                       (uu___1930_77848.FStar_TypeChecker_Env.gamma_sig);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___1930_77848.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___1930_77848.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___1930_77848.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___1930_77848.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.attrtab =
                       (uu___1930_77848.FStar_TypeChecker_Env.attrtab);
                     FStar_TypeChecker_Env.is_pattern =
                       (uu___1930_77848.FStar_TypeChecker_Env.is_pattern);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___1930_77848.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___1930_77848.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___1930_77848.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___1930_77848.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___1930_77848.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___1930_77848.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___1930_77848.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___1930_77848.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___1930_77848.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax = true;
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___1930_77848.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.phase1 =
                       (uu___1930_77848.FStar_TypeChecker_Env.phase1);
                     FStar_TypeChecker_Env.failhard =
                       (uu___1930_77848.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___1930_77848.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.uvar_subtyping =
                       (uu___1930_77848.FStar_TypeChecker_Env.uvar_subtyping);
                     FStar_TypeChecker_Env.tc_term =
                       (uu___1930_77848.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.type_of =
                       (uu___1930_77848.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___1930_77848.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.check_type_of =
                       (uu___1930_77848.FStar_TypeChecker_Env.check_type_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___1930_77848.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (uu___1930_77848.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (uu___1930_77848.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.fv_delta_depths =
                       (uu___1930_77848.FStar_TypeChecker_Env.fv_delta_depths);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___1930_77848.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (uu___1930_77848.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.splice =
                       (uu___1930_77848.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.postprocess =
                       (uu___1930_77848.FStar_TypeChecker_Env.postprocess);
                     FStar_TypeChecker_Env.is_native_tactic =
                       (uu___1930_77848.FStar_TypeChecker_Env.is_native_tactic);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___1930_77848.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (uu___1930_77848.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (uu___1930_77848.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.nbe =
                       (uu___1930_77848.FStar_TypeChecker_Env.nbe)
                   }) t
                 in
              match uu____77839 with
              | (t1,lcomp,g) ->
                  let uu____77855 =
                    (let uu____77859 =
                       FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                     Prims.op_Negation uu____77859) ||
                      (let uu____77862 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____77862)
                     in
                  if uu____77855
                  then ret t1
                  else
                    (let rewrite_eq =
                       let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                       let uu____77873 = new_uvar "pointwise_rec" env typ  in
                       bind uu____77873
                         (fun uu____77890  ->
                            match uu____77890 with
                            | (ut,uvar_ut) ->
                                (log ps
                                   (fun uu____77903  ->
                                      let uu____77904 =
                                        FStar_Syntax_Print.term_to_string t1
                                         in
                                      let uu____77906 =
                                        FStar_Syntax_Print.term_to_string ut
                                         in
                                      FStar_Util.print2
                                        "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                        uu____77904 uu____77906);
                                 (let uu____77909 =
                                    let uu____77912 =
                                      let uu____77913 =
                                        FStar_TypeChecker_TcTerm.universe_of
                                          env typ
                                         in
                                      FStar_Syntax_Util.mk_eq2 uu____77913
                                        typ t1 ut
                                       in
                                    add_irrelevant_goal
                                      "pointwise_rec equation" env
                                      uu____77912 opts label1
                                     in
                                  bind uu____77909
                                    (fun uu____77917  ->
                                       let uu____77918 =
                                         bind tau
                                           (fun uu____77924  ->
                                              let ut1 =
                                                FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                  env ut
                                                 in
                                              log ps
                                                (fun uu____77930  ->
                                                   let uu____77931 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1
                                                      in
                                                   let uu____77933 =
                                                     FStar_Syntax_Print.term_to_string
                                                       ut1
                                                      in
                                                   FStar_Util.print2
                                                     "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                     uu____77931 uu____77933);
                                              ret ut1)
                                          in
                                       focus uu____77918))))
                        in
                     let uu____77936 = catch rewrite_eq  in
                     bind uu____77936
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
          let uu____78154 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____78154
            (fun t1  ->
               let uu____78162 =
                 f env
                   (let uu___2007_78171 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___2007_78171.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___2007_78171.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____78162
                 (fun uu____78187  ->
                    match uu____78187 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____78210 =
                               let uu____78211 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____78211.FStar_Syntax_Syntax.n  in
                             match uu____78210 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____78248 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____78248
                                   (fun uu____78273  ->
                                      match uu____78273 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____78289 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____78289
                                            (fun uu____78316  ->
                                               match uu____78316 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___1987_78346 =
                                                         t3  in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___1987_78346.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___1987_78346.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____78388 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____78388 with
                                  | (bs1,t') ->
                                      let uu____78403 =
                                        let uu____78410 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____78410 ctrl1 t'
                                         in
                                      bind uu____78403
                                        (fun uu____78428  ->
                                           match uu____78428 with
                                           | (t'',ctrl2) ->
                                               let uu____78443 =
                                                 let uu____78450 =
                                                   let uu___2000_78453 = t4
                                                      in
                                                   let uu____78456 =
                                                     let uu____78457 =
                                                       let uu____78476 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____78485 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____78476,
                                                         uu____78485, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____78457
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____78456;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___2000_78453.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___2000_78453.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____78450, ctrl2)  in
                                               ret uu____78443))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____78538 -> ret (t3, ctrl1))))

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
              let uu____78585 = ctrl_tac_fold f env ctrl t  in
              bind uu____78585
                (fun uu____78609  ->
                   match uu____78609 with
                   | (t1,ctrl1) ->
                       let uu____78624 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____78624
                         (fun uu____78651  ->
                            match uu____78651 with
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
                let uu____78745 =
                  let uu____78753 =
                    add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                      opts label1
                     in
                  bind uu____78753
                    (fun uu____78764  ->
                       let uu____78765 = ctrl t1  in
                       bind uu____78765
                         (fun res  ->
                            let uu____78792 = trivial ()  in
                            bind uu____78792 (fun uu____78801  -> ret res)))
                   in
                bind uu____78745
                  (fun uu____78819  ->
                     match uu____78819 with
                     | (should_rewrite,ctrl1) ->
                         if Prims.op_Negation should_rewrite
                         then ret (t1, ctrl1)
                         else
                           (let uu____78848 =
                              FStar_TypeChecker_TcTerm.tc_term
                                (let uu___2037_78857 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___2037_78857.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___2037_78857.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___2037_78857.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___2037_78857.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___2037_78857.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___2037_78857.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___2037_78857.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___2037_78857.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___2037_78857.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___2037_78857.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___2037_78857.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___2037_78857.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___2037_78857.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___2037_78857.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___2037_78857.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___2037_78857.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___2037_78857.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___2037_78857.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___2037_78857.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___2037_78857.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___2037_78857.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___2037_78857.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___2037_78857.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___2037_78857.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___2037_78857.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___2037_78857.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___2037_78857.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___2037_78857.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___2037_78857.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___2037_78857.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___2037_78857.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___2037_78857.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___2037_78857.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___2037_78857.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___2037_78857.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___2037_78857.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___2037_78857.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___2037_78857.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___2037_78857.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___2037_78857.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___2037_78857.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___2037_78857.FStar_TypeChecker_Env.nbe)
                                 }) t1
                               in
                            match uu____78848 with
                            | (t2,lcomp,g) ->
                                let uu____78868 =
                                  (let uu____78872 =
                                     FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                       lcomp
                                      in
                                   Prims.op_Negation uu____78872) ||
                                    (let uu____78875 =
                                       FStar_TypeChecker_Env.is_trivial g  in
                                     Prims.op_Negation uu____78875)
                                   in
                                if uu____78868
                                then ret (t2, globalStop)
                                else
                                  (let typ =
                                     lcomp.FStar_Syntax_Syntax.res_typ  in
                                   let uu____78891 =
                                     new_uvar "pointwise_rec" env typ  in
                                   bind uu____78891
                                     (fun uu____78912  ->
                                        match uu____78912 with
                                        | (ut,uvar_ut) ->
                                            (log ps
                                               (fun uu____78929  ->
                                                  let uu____78930 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t2
                                                     in
                                                  let uu____78932 =
                                                    FStar_Syntax_Print.term_to_string
                                                      ut
                                                     in
                                                  FStar_Util.print2
                                                    "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                    uu____78930 uu____78932);
                                             (let uu____78935 =
                                                let uu____78938 =
                                                  let uu____78939 =
                                                    FStar_TypeChecker_TcTerm.universe_of
                                                      env typ
                                                     in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____78939 typ t2 ut
                                                   in
                                                add_irrelevant_goal
                                                  "rewrite_rec equation" env
                                                  uu____78938 opts label1
                                                 in
                                              bind uu____78935
                                                (fun uu____78947  ->
                                                   let uu____78948 =
                                                     bind rewriter
                                                       (fun uu____78962  ->
                                                          let ut1 =
                                                            FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                              env ut
                                                             in
                                                          log ps
                                                            (fun uu____78968 
                                                               ->
                                                               let uu____78969
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   t2
                                                                  in
                                                               let uu____78971
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   ut1
                                                                  in
                                                               FStar_Util.print2
                                                                 "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                                 uu____78969
                                                                 uu____78971);
                                                          ret (ut1, ctrl1))
                                                      in
                                                   focus uu____78948)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term -> (Prims.bool * FStar_BigInt.t) tac) ->
    unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____79017 =
        bind get
          (fun ps  ->
             let uu____79027 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____79027 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____79065  ->
                       let uu____79066 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____79066);
                  bind dismiss_all
                    (fun uu____79071  ->
                       let uu____79072 =
                         let uu____79079 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____79079
                           keepGoing gt1
                          in
                       bind uu____79072
                         (fun uu____79091  ->
                            match uu____79091 with
                            | (gt',uu____79099) ->
                                (log ps
                                   (fun uu____79103  ->
                                      let uu____79104 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____79104);
                                 (let uu____79107 = push_goals gs  in
                                  bind uu____79107
                                    (fun uu____79112  ->
                                       let uu____79113 =
                                         let uu____79116 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____79116]  in
                                       add_goals uu____79113)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____79017
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____79141 =
        bind get
          (fun ps  ->
             let uu____79151 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____79151 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____79189  ->
                       let uu____79190 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____79190);
                  bind dismiss_all
                    (fun uu____79195  ->
                       let uu____79196 =
                         let uu____79199 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____79199 gt1
                          in
                       bind uu____79196
                         (fun gt'  ->
                            log ps
                              (fun uu____79207  ->
                                 let uu____79208 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____79208);
                            (let uu____79211 = push_goals gs  in
                             bind uu____79211
                               (fun uu____79216  ->
                                  let uu____79217 =
                                    let uu____79220 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____79220]  in
                                  add_goals uu____79217))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____79141
  
let (trefl : unit -> unit tac) =
  fun uu____79233  ->
    let uu____79236 =
      let uu____79239 = cur_goal ()  in
      bind uu____79239
        (fun g  ->
           let uu____79257 =
             let uu____79262 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____79262  in
           match uu____79257 with
           | FStar_Pervasives_Native.Some t ->
               let uu____79270 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____79270 with
                | (hd1,args) ->
                    let uu____79309 =
                      let uu____79322 =
                        let uu____79323 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____79323.FStar_Syntax_Syntax.n  in
                      (uu____79322, args)  in
                    (match uu____79309 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____79337::(l,uu____79339)::(r,uu____79341)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____79388 =
                           let uu____79392 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____79392 l r  in
                         bind uu____79388
                           (fun b  ->
                              if b
                              then solve' g FStar_Syntax_Util.exp_unit
                              else
                                (let l1 =
                                   let uu____79403 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____79403 l
                                    in
                                 let r1 =
                                   let uu____79405 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____79405 r
                                    in
                                 let uu____79406 =
                                   let uu____79410 =
                                     FStar_Tactics_Types.goal_env g  in
                                   do_unify uu____79410 l1 r1  in
                                 bind uu____79406
                                   (fun b1  ->
                                      if b1
                                      then
                                        solve' g FStar_Syntax_Util.exp_unit
                                      else
                                        (let uu____79420 =
                                           let uu____79422 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____79422 l1  in
                                         let uu____79423 =
                                           let uu____79425 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____79425 r1  in
                                         fail2
                                           "not a trivial equality ((%s) vs (%s))"
                                           uu____79420 uu____79423))))
                     | (hd2,uu____79428) ->
                         let uu____79445 =
                           let uu____79447 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____79447 t  in
                         fail1 "trefl: not an equality (%s)" uu____79445))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____79236
  
let (dup : unit -> unit tac) =
  fun uu____79464  ->
    let uu____79467 = cur_goal ()  in
    bind uu____79467
      (fun g  ->
         let uu____79473 =
           let uu____79480 = FStar_Tactics_Types.goal_env g  in
           let uu____79481 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____79480 uu____79481  in
         bind uu____79473
           (fun uu____79491  ->
              match uu____79491 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___2129_79501 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___2129_79501.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___2129_79501.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___2129_79501.FStar_Tactics_Types.is_guard);
                      FStar_Tactics_Types.label =
                        (uu___2129_79501.FStar_Tactics_Types.label)
                    }  in
                  bind __dismiss
                    (fun uu____79504  ->
                       let uu____79505 =
                         let uu____79508 = FStar_Tactics_Types.goal_env g  in
                         let uu____79509 =
                           let uu____79510 =
                             let uu____79511 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____79512 =
                               FStar_Tactics_Types.goal_type g  in
                             FStar_TypeChecker_TcTerm.universe_of uu____79511
                               uu____79512
                              in
                           let uu____79513 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____79514 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____79510 uu____79513 u
                             uu____79514
                            in
                         add_irrelevant_goal "dup equation" uu____79508
                           uu____79509 g.FStar_Tactics_Types.opts
                           g.FStar_Tactics_Types.label
                          in
                       bind uu____79505
                         (fun uu____79518  ->
                            let uu____79519 = add_goals [g']  in
                            bind uu____79519 (fun uu____79523  -> ret ())))))
  
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
              let uu____79649 = f x y  in
              if uu____79649 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____79672 -> (acc, l11, l21)  in
        let uu____79687 = aux [] l1 l2  in
        match uu____79687 with | (pr,t1,t2) -> ((FStar_List.rev pr), t1, t2)
  
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
      let uu____79793 = get_phi g1  in
      match uu____79793 with
      | FStar_Pervasives_Native.None  -> fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____79800 = get_phi g2  in
          (match uu____79800 with
           | FStar_Pervasives_Native.None  -> fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let uu____79813 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2)
                  in
               (match uu____79813 with
                | (gamma,r1,r2) ->
                    let t1 =
                      let uu____79844 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1)
                         in
                      close_forall_no_univs1 uu____79844 phi1  in
                    let t2 =
                      let uu____79854 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2)
                         in
                      close_forall_no_univs1 uu____79854 phi2  in
                    let uu____79863 =
                      set_solution g1 FStar_Syntax_Util.exp_unit  in
                    bind uu____79863
                      (fun uu____79868  ->
                         let uu____79869 =
                           set_solution g2 FStar_Syntax_Util.exp_unit  in
                         bind uu____79869
                           (fun uu____79876  ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2  in
                              let nenv =
                                let uu___2180_79881 =
                                  FStar_Tactics_Types.goal_env g1  in
                                let uu____79882 =
                                  FStar_Util.smap_create
                                    (Prims.parse_int "100")
                                   in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___2180_79881.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___2180_79881.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___2180_79881.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___2180_79881.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____79882;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___2180_79881.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___2180_79881.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___2180_79881.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___2180_79881.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___2180_79881.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___2180_79881.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___2180_79881.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___2180_79881.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___2180_79881.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___2180_79881.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___2180_79881.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___2180_79881.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___2180_79881.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___2180_79881.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___2180_79881.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___2180_79881.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___2180_79881.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___2180_79881.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___2180_79881.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___2180_79881.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___2180_79881.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___2180_79881.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___2180_79881.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___2180_79881.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___2180_79881.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___2180_79881.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___2180_79881.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___2180_79881.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___2180_79881.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___2180_79881.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___2180_79881.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___2180_79881.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___2180_79881.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___2180_79881.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___2180_79881.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___2180_79881.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___2180_79881.FStar_TypeChecker_Env.nbe)
                                }  in
                              let uu____79886 =
                                mk_irrelevant_goal "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                  g1.FStar_Tactics_Types.label
                                 in
                              bind uu____79886
                                (fun goal  ->
                                   mlog
                                     (fun uu____79896  ->
                                        let uu____79897 =
                                          goal_to_string_verbose g1  in
                                        let uu____79899 =
                                          goal_to_string_verbose g2  in
                                        let uu____79901 =
                                          goal_to_string_verbose goal  in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____79897 uu____79899 uu____79901)
                                     (fun uu____79905  -> ret goal))))))
  
let (join : unit -> unit tac) =
  fun uu____79913  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____79929 =
               set
                 (let uu___2195_79934 = ps  in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___2195_79934.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.main_goal =
                      (uu___2195_79934.FStar_Tactics_Types.main_goal);
                    FStar_Tactics_Types.all_implicits =
                      (uu___2195_79934.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___2195_79934.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___2195_79934.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___2195_79934.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___2195_79934.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___2195_79934.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___2195_79934.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___2195_79934.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___2195_79934.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___2195_79934.FStar_Tactics_Types.local_state)
                  })
                in
             bind uu____79929
               (fun uu____79937  ->
                  let uu____79938 = join_goals g1 g2  in
                  bind uu____79938 (fun g12  -> add_goals [g12]))
         | uu____79943 -> fail "join: less than 2 goals")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) tac)
  =
  fun t  ->
    let uu____79965 =
      let uu____79972 = cur_goal ()  in
      bind uu____79972
        (fun g  ->
           let uu____79982 =
             let uu____79991 = FStar_Tactics_Types.goal_env g  in
             __tc uu____79991 t  in
           bind uu____79982
             (fun uu____80019  ->
                match uu____80019 with
                | (t1,typ,guard) ->
                    let uu____80035 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____80035 with
                     | (hd1,args) ->
                         let uu____80084 =
                           let uu____80099 =
                             let uu____80100 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____80100.FStar_Syntax_Syntax.n  in
                           (uu____80099, args)  in
                         (match uu____80084 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____80121)::(q,uu____80123)::[]) when
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
                                let uu____80177 =
                                  let uu____80178 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____80178
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____80177
                                 in
                              let g2 =
                                let uu____80180 =
                                  let uu____80181 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____80181
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____80180
                                 in
                              bind __dismiss
                                (fun uu____80188  ->
                                   let uu____80189 = add_goals [g1; g2]  in
                                   bind uu____80189
                                     (fun uu____80198  ->
                                        let uu____80199 =
                                          let uu____80204 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____80205 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____80204, uu____80205)  in
                                        ret uu____80199))
                          | uu____80210 ->
                              let uu____80225 =
                                let uu____80227 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____80227 typ  in
                              fail1 "Not a disjunction: %s" uu____80225))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____79965
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____80262 =
      let uu____80265 = cur_goal ()  in
      bind uu____80265
        (fun g  ->
           FStar_Options.push ();
           (let uu____80278 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____80278);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___2232_80285 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___2232_80285.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___2232_80285.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___2232_80285.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___2232_80285.FStar_Tactics_Types.label)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____80262
  
let (top_env : unit -> env tac) =
  fun uu____80302  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____80317  ->
    let uu____80321 = cur_goal ()  in
    bind uu____80321
      (fun g  ->
         let uu____80328 =
           (FStar_Options.lax ()) ||
             (let uu____80331 = FStar_Tactics_Types.goal_env g  in
              uu____80331.FStar_TypeChecker_Env.lax)
            in
         ret uu____80328)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____80348 =
        mlog
          (fun uu____80353  ->
             let uu____80354 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____80354)
          (fun uu____80359  ->
             let uu____80360 = cur_goal ()  in
             bind uu____80360
               (fun goal  ->
                  let env =
                    let uu____80368 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____80368 ty  in
                  let uu____80369 = __tc_ghost env tm  in
                  bind uu____80369
                    (fun uu____80388  ->
                       match uu____80388 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____80402  ->
                                let uu____80403 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____80403)
                             (fun uu____80407  ->
                                mlog
                                  (fun uu____80410  ->
                                     let uu____80411 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____80411)
                                  (fun uu____80416  ->
                                     let uu____80417 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____80417
                                       (fun uu____80422  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____80348
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____80447 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____80453 =
              let uu____80460 =
                let uu____80461 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____80461
                 in
              new_uvar "uvar_env.2" env uu____80460  in
            bind uu____80453
              (fun uu____80478  ->
                 match uu____80478 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____80447
        (fun typ  ->
           let uu____80490 = new_uvar "uvar_env" env typ  in
           bind uu____80490
             (fun uu____80505  ->
                match uu____80505 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____80524 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____80543 -> g.FStar_Tactics_Types.opts
             | uu____80546 -> FStar_Options.peek ()  in
           let uu____80549 = FStar_Syntax_Util.head_and_args t  in
           match uu____80549 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____80569);
                FStar_Syntax_Syntax.pos = uu____80570;
                FStar_Syntax_Syntax.vars = uu____80571;_},uu____80572)
               ->
               let env1 =
                 let uu___2286_80614 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___2286_80614.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___2286_80614.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___2286_80614.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___2286_80614.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___2286_80614.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___2286_80614.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___2286_80614.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___2286_80614.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___2286_80614.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___2286_80614.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___2286_80614.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___2286_80614.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___2286_80614.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___2286_80614.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___2286_80614.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___2286_80614.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___2286_80614.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___2286_80614.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___2286_80614.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___2286_80614.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___2286_80614.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___2286_80614.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___2286_80614.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___2286_80614.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___2286_80614.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___2286_80614.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___2286_80614.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___2286_80614.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___2286_80614.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___2286_80614.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___2286_80614.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___2286_80614.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___2286_80614.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___2286_80614.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___2286_80614.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___2286_80614.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___2286_80614.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___2286_80614.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___2286_80614.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___2286_80614.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___2286_80614.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___2286_80614.FStar_TypeChecker_Env.nbe)
                 }  in
               let g =
                 FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false ""  in
               let uu____80618 =
                 let uu____80621 = bnorm_goal g  in [uu____80621]  in
               add_goals uu____80618
           | uu____80622 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____80524
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____80684 = if b then t2 else ret false  in
             bind uu____80684 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____80710 = trytac comp  in
      bind uu____80710
        (fun uu___613_80722  ->
           match uu___613_80722 with
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
        let uu____80764 =
          bind get
            (fun ps  ->
               let uu____80772 = __tc e t1  in
               bind uu____80772
                 (fun uu____80793  ->
                    match uu____80793 with
                    | (t11,ty1,g1) ->
                        let uu____80806 = __tc e t2  in
                        bind uu____80806
                          (fun uu____80827  ->
                             match uu____80827 with
                             | (t21,ty2,g2) ->
                                 let uu____80840 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____80840
                                   (fun uu____80847  ->
                                      let uu____80848 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____80848
                                        (fun uu____80856  ->
                                           let uu____80857 =
                                             do_unify e ty1 ty2  in
                                           let uu____80861 =
                                             do_unify e t11 t21  in
                                           tac_and uu____80857 uu____80861)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____80764
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____80909  ->
             let uu____80910 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____80910
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
        (fun uu____80944  ->
           let uu____80945 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____80945)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____80956 =
      mlog
        (fun uu____80961  ->
           let uu____80962 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____80962)
        (fun uu____80967  ->
           let uu____80968 = cur_goal ()  in
           bind uu____80968
             (fun g  ->
                let uu____80974 =
                  let uu____80983 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____80983 ty  in
                bind uu____80974
                  (fun uu____80995  ->
                     match uu____80995 with
                     | (ty1,uu____81005,guard) ->
                         let uu____81007 =
                           let uu____81010 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____81010 guard  in
                         bind uu____81007
                           (fun uu____81014  ->
                              let uu____81015 =
                                let uu____81019 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____81020 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____81019 uu____81020 ty1  in
                              bind uu____81015
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____81029 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____81029
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops]  in
                                      let ng =
                                        let uu____81036 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____81037 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____81036
                                          uu____81037
                                         in
                                      let nty =
                                        let uu____81039 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____81039 ty1  in
                                      let uu____81040 =
                                        let uu____81044 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____81044 ng nty  in
                                      bind uu____81040
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____81053 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____81053
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____80956
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) Prims.list tac)
  =
  fun s_tm  ->
    let uu____81127 =
      let uu____81136 = cur_goal ()  in
      bind uu____81136
        (fun g  ->
           let uu____81148 =
             let uu____81157 = FStar_Tactics_Types.goal_env g  in
             __tc uu____81157 s_tm  in
           bind uu____81148
             (fun uu____81175  ->
                match uu____81175 with
                | (s_tm1,s_ty,guard) ->
                    let uu____81193 =
                      let uu____81196 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____81196 guard  in
                    bind uu____81193
                      (fun uu____81209  ->
                         let uu____81210 =
                           FStar_Syntax_Util.head_and_args' s_ty  in
                         match uu____81210 with
                         | (h,args) ->
                             let uu____81255 =
                               let uu____81262 =
                                 let uu____81263 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____81263.FStar_Syntax_Syntax.n  in
                               match uu____81262 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____81278;
                                      FStar_Syntax_Syntax.vars = uu____81279;_},us)
                                   -> ret (fv, us)
                               | uu____81289 -> fail "type is not an fv"  in
                             bind uu____81255
                               (fun uu____81310  ->
                                  match uu____81310 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____81326 =
                                        let uu____81329 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____81329 t_lid
                                         in
                                      (match uu____81326 with
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
                                                  (fun uu____81380  ->
                                                     let uu____81381 =
                                                       FStar_Syntax_Subst.open_term
                                                         t_ps t_ty
                                                        in
                                                     match uu____81381 with
                                                     | (t_ps1,t_ty1) ->
                                                         let uu____81396 =
                                                           mapM
                                                             (fun c_lid  ->
                                                                let uu____81424
                                                                  =
                                                                  let uu____81427
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                  FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____81427
                                                                    c_lid
                                                                   in
                                                                match uu____81424
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
                                                                    uu____81501
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
                                                                    let uu____81506
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____81506
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____81529
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____81529
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____81572
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs
                                                                     in
                                                                    (match uu____81572
                                                                    with
                                                                    | 
                                                                    (d_ps,bs1)
                                                                    ->
                                                                    let uu____81645
                                                                    =
                                                                    let uu____81647
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp  in
                                                                    Prims.op_Negation
                                                                    uu____81647
                                                                     in
                                                                    failwhen
                                                                    uu____81645
                                                                    "not total?"
                                                                    (fun
                                                                    uu____81666
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
                                                                    uu___614_81683
                                                                    =
                                                                    match uu___614_81683
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____81687)
                                                                    -> true
                                                                    | 
                                                                    uu____81690
                                                                    -> false
                                                                     in
                                                                    let uu____81694
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____81694
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
                                                                    uu____81828
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
                                                                    uu____81890
                                                                     ->
                                                                    match uu____81890
                                                                    with
                                                                    | 
                                                                    ((bv,uu____81910),
                                                                    (t,uu____81912))
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
                                                                    uu____81982
                                                                     ->
                                                                    match uu____81982
                                                                    with
                                                                    | 
                                                                    ((bv,uu____82009),
                                                                    (t,uu____82011))
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
                                                                    uu____82070
                                                                     ->
                                                                    match uu____82070
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
                                                                    let uu____82125
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___2450_82142
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___2450_82142.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___2450_82142.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___2450_82142.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___2450_82142.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___2450_82142.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___2450_82142.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___2450_82142.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___2450_82142.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___2450_82142.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___2450_82142.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___2450_82142.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___2450_82142.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___2450_82142.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___2450_82142.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___2450_82142.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___2450_82142.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___2450_82142.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___2450_82142.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___2450_82142.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___2450_82142.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___2450_82142.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___2450_82142.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___2450_82142.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___2450_82142.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___2450_82142.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___2450_82142.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___2450_82142.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___2450_82142.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___2450_82142.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___2450_82142.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___2450_82142.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___2450_82142.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___2450_82142.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___2450_82142.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___2450_82142.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___2450_82142.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___2450_82142.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___2450_82142.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___2450_82142.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___2450_82142.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___2450_82142.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___2450_82142.FStar_TypeChecker_Env.nbe)
                                                                    }) s_ty
                                                                    pat  in
                                                                    match uu____82125
                                                                    with
                                                                    | 
                                                                    (uu____82156,uu____82157,uu____82158,pat_t,uu____82160,_guard_pat)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____82167
                                                                    =
                                                                    let uu____82168
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____82168
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____82167
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____82173
                                                                    =
                                                                    let uu____82182
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____82182]
                                                                     in
                                                                    let uu____82201
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____82173
                                                                    uu____82201
                                                                     in
                                                                    let nty =
                                                                    let uu____82207
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____82207
                                                                     in
                                                                    let uu____82210
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____82210
                                                                    (fun
                                                                    uu____82240
                                                                     ->
                                                                    match uu____82240
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
                                                                    let uu____82267
                                                                    =
                                                                    let uu____82278
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____82278]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____82267
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____82314
                                                                    =
                                                                    let uu____82325
                                                                    =
                                                                    let uu____82330
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2)  in
                                                                    (fv1,
                                                                    uu____82330)
                                                                     in
                                                                    (g', br,
                                                                    uu____82325)
                                                                     in
                                                                    ret
                                                                    uu____82314))))))
                                                                    | 
                                                                    uu____82351
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                             c_lids
                                                            in
                                                         bind uu____81396
                                                           (fun goal_brs  ->
                                                              let uu____82401
                                                                =
                                                                FStar_List.unzip3
                                                                  goal_brs
                                                                 in
                                                              match uu____82401
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
                                                                  let uu____82474
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                  bind
                                                                    uu____82474
                                                                    (
                                                                    fun
                                                                    uu____82485
                                                                     ->
                                                                    let uu____82486
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____82486
                                                                    (fun
                                                                    uu____82496
                                                                     ->
                                                                    ret infos))))
                                            | uu____82503 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____81127
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____82552::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____82582 = init xs  in x :: uu____82582
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____82595 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      let t3 = FStar_Syntax_Util.unlazy_emb t2  in
      match t3.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____82604) -> inspect t4
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____82670 = last args  in
          (match uu____82670 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____82700 =
                 let uu____82701 =
                   let uu____82706 =
                     let uu____82707 =
                       let uu____82712 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____82712  in
                     uu____82707 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____82706, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____82701  in
               FStar_All.pipe_left ret uu____82700)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____82725,uu____82726) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
          let uu____82779 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____82779 with
           | (bs1,t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____82821 =
                      let uu____82822 =
                        let uu____82827 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____82827)  in
                      FStar_Reflection_Data.Tv_Abs uu____82822  in
                    FStar_All.pipe_left ret uu____82821))
      | FStar_Syntax_Syntax.Tm_type uu____82830 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____82855 ->
          let uu____82870 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____82870 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____82901 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____82901 with
           | (b',t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____82954 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____82967 =
            let uu____82968 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____82968  in
          FStar_All.pipe_left ret uu____82967
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____82989 =
            let uu____82990 =
              let uu____82995 =
                let uu____82996 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____82996  in
              (uu____82995, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____82990  in
          FStar_All.pipe_left ret uu____82989
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____83036 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____83041 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____83041 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____83094 ->
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
             | FStar_Util.Inr uu____83136 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____83140 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____83140 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____83160 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____83166 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____83221 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____83221
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____83242 =
                  let uu____83249 =
                    FStar_List.map
                      (fun uu____83262  ->
                         match uu____83262 with
                         | (p1,uu____83271) -> inspect_pat p1) ps
                     in
                  (fv, uu____83249)  in
                FStar_Reflection_Data.Pat_Cons uu____83242
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
              (fun uu___615_83367  ->
                 match uu___615_83367 with
                 | (pat,uu____83389,t5) ->
                     let uu____83407 = inspect_pat pat  in (uu____83407, t5))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____83416 ->
          ((let uu____83418 =
              let uu____83424 =
                let uu____83426 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____83428 = FStar_Syntax_Print.term_to_string t3  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____83426 uu____83428
                 in
              (FStar_Errors.Warning_CantInspect, uu____83424)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____83418);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____82595
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____83446 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____83446
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____83450 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____83450
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____83454 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____83454
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____83461 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____83461
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____83486 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____83486
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____83503 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____83503
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____83522 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____83522
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____83526 =
          let uu____83527 =
            let uu____83534 =
              let uu____83535 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____83535  in
            FStar_Syntax_Syntax.mk uu____83534  in
          uu____83527 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____83526
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____83543 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____83543
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____83554 =
          let uu____83555 =
            let uu____83562 =
              let uu____83563 =
                let uu____83577 =
                  let uu____83580 =
                    let uu____83581 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____83581]  in
                  FStar_Syntax_Subst.close uu____83580 t2  in
                ((false, [lb]), uu____83577)  in
              FStar_Syntax_Syntax.Tm_let uu____83563  in
            FStar_Syntax_Syntax.mk uu____83562  in
          uu____83555 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____83554
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____83626 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____83626 with
         | (lbs,body) ->
             let uu____83641 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____83641)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____83678 =
                let uu____83679 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____83679  in
              FStar_All.pipe_left wrap uu____83678
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____83686 =
                let uu____83687 =
                  let uu____83701 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____83719 = pack_pat p1  in
                         (uu____83719, false)) ps
                     in
                  (fv, uu____83701)  in
                FStar_Syntax_Syntax.Pat_cons uu____83687  in
              FStar_All.pipe_left wrap uu____83686
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
            (fun uu___616_83768  ->
               match uu___616_83768 with
               | (pat,t1) ->
                   let uu____83785 = pack_pat pat  in
                   (uu____83785, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____83833 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____83833
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____83861 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____83861
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____83907 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____83907
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____83946 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____83946
  
let (lget :
  FStar_Reflection_Data.typ -> Prims.string -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun k  ->
      let uu____83966 =
        bind get
          (fun ps  ->
             let uu____83972 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____83972 with
             | FStar_Pervasives_Native.None  -> fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
      FStar_All.pipe_left (wrap_err "lget") uu____83966
  
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit tac)
  =
  fun _ty  ->
    fun k  ->
      fun t  ->
        let uu____84006 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___2748_84013 = ps  in
                 let uu____84014 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t
                    in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___2748_84013.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___2748_84013.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___2748_84013.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___2748_84013.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___2748_84013.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___2748_84013.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___2748_84013.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___2748_84013.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___2748_84013.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___2748_84013.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___2748_84013.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___2748_84013.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____84014
                 }  in
               set ps1)
           in
        FStar_All.pipe_left (wrap_err "lset") uu____84006
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal * FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun typ  ->
      let uu____84041 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____84041 with
      | (u,ctx_uvars,g_u) ->
          let uu____84074 = FStar_List.hd ctx_uvars  in
          (match uu____84074 with
           | (ctx_uvar,uu____84088) ->
               let g =
                 let uu____84090 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____84090 false
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
        let uu____84113 = goal_of_goal_ty env typ  in
        match uu____84113 with
        | (g,g_u) ->
            let ps =
              let uu____84125 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "TacVerbose")
                 in
              let uu____84128 = FStar_Util.psmap_empty ()  in
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
                FStar_Tactics_Types.tac_verb_dbg = uu____84125;
                FStar_Tactics_Types.local_state = uu____84128
              }  in
            let uu____84138 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____84138)
  