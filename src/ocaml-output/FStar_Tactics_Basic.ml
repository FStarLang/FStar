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
    let uu____63887 =
      let uu____63888 = FStar_Tactics_Types.goal_env g  in
      let uu____63889 = FStar_Tactics_Types.goal_type g  in
      bnorm uu____63888 uu____63889  in
    FStar_Tactics_Types.goal_with_type g uu____63887
  
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
      let uu____64003 = FStar_Options.tactics_failhard ()  in
      if uu____64003
      then run t p
      else
        (try (fun uu___640_64013  -> match () with | () -> run t p) ()
         with
         | FStar_Errors.Err (uu____64022,msg) ->
             FStar_Tactics_Result.Failed
               ((FStar_Tactics_Types.TacticFailure msg), p)
         | FStar_Errors.Error (uu____64026,msg,uu____64028) ->
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
           let uu____64108 = run t1 p  in
           match uu____64108 with
           | FStar_Tactics_Result.Success (a,q) ->
               let uu____64115 = t2 a  in run uu____64115 q
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
    let uu____64138 =
      FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head  in
    match uu____64138 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (check_goal_solved :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun goal  -> get_uvar_solved goal.FStar_Tactics_Types.goal_ctx_uvar 
let (goal_to_string_verbose : FStar_Tactics_Types.goal -> Prims.string) =
  fun g  ->
    let uu____64160 =
      FStar_Syntax_Print.ctx_uvar_to_string
        g.FStar_Tactics_Types.goal_ctx_uvar
       in
    let uu____64162 =
      let uu____64164 = check_goal_solved g  in
      match uu____64164 with
      | FStar_Pervasives_Native.None  -> ""
      | FStar_Pervasives_Native.Some t ->
          let uu____64170 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "\tGOAL ALREADY SOLVED!: %s" uu____64170
       in
    FStar_Util.format2 "%s%s\n" uu____64160 uu____64162
  
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
            let uu____64217 = FStar_Options.print_implicits ()  in
            if uu____64217
            then
              let uu____64221 = FStar_Tactics_Types.goal_env g  in
              let uu____64222 = FStar_Tactics_Types.goal_witness g  in
              tts uu____64221 uu____64222
            else
              (let uu____64225 =
                 get_uvar_solved g.FStar_Tactics_Types.goal_ctx_uvar  in
               match uu____64225 with
               | FStar_Pervasives_Native.None  -> "_"
               | FStar_Pervasives_Native.Some t ->
                   let uu____64231 = FStar_Tactics_Types.goal_env g  in
                   let uu____64232 = FStar_Tactics_Types.goal_witness g  in
                   tts uu____64231 uu____64232)
             in
          let num =
            match maybe_num with
            | FStar_Pervasives_Native.None  -> ""
            | FStar_Pervasives_Native.Some (i,n1) ->
                let uu____64255 = FStar_Util.string_of_int i  in
                let uu____64257 = FStar_Util.string_of_int n1  in
                FStar_Util.format2 " %s/%s" uu____64255 uu____64257
             in
          let maybe_label =
            match g.FStar_Tactics_Types.label with
            | "" -> ""
            | l -> Prims.op_Hat " (" (Prims.op_Hat l ")")  in
          let actual_goal =
            if ps.FStar_Tactics_Types.tac_verb_dbg
            then goal_to_string_verbose g
            else
              (let uu____64275 =
                 FStar_Syntax_Print.binders_to_string ", "
                   (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
                  in
               let uu____64278 =
                 let uu____64280 = FStar_Tactics_Types.goal_env g  in
                 tts uu____64280
                   (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                  in
               FStar_Util.format3 "%s |- %s : %s\n" uu____64275 w uu____64278)
             in
          FStar_Util.format4 "%s%s%s:\n%s\n" kind num maybe_label actual_goal
  
let (tacprint : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      let uu____64307 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____64307
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____64332 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____64332
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____64364 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____64364
  
let (comp_to_typ : FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____64374) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____64384) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (get_phi :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun g  ->
    let uu____64404 =
      let uu____64405 = FStar_Tactics_Types.goal_env g  in
      let uu____64406 = FStar_Tactics_Types.goal_type g  in
      FStar_TypeChecker_Normalize.unfold_whnf uu____64405 uu____64406  in
    FStar_Syntax_Util.un_squash uu____64404
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  -> let uu____64415 = get_phi g  in FStar_Option.isSome uu____64415 
let (print : Prims.string -> unit tac) = fun msg  -> tacprint msg; ret () 
let (debugging : unit -> Prims.bool tac) =
  fun uu____64439  ->
    bind get
      (fun ps  ->
         let uu____64447 =
           FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
             (FStar_Options.Other "Tac")
            in
         ret uu____64447)
  
let (ps_to_string :
  (Prims.string * FStar_Tactics_Types.proofstate) -> Prims.string) =
  fun uu____64462  ->
    match uu____64462 with
    | (msg,ps) ->
        let p_imp imp =
          FStar_Syntax_Print.uvar_to_string
            (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
           in
        let n_active = FStar_List.length ps.FStar_Tactics_Types.goals  in
        let n_smt = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
        let n1 = n_active + n_smt  in
        let uu____64484 =
          let uu____64488 =
            let uu____64492 =
              let uu____64494 =
                FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
              FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____64494
                msg
               in
            let uu____64497 =
              let uu____64501 =
                if
                  ps.FStar_Tactics_Types.entry_range <>
                    FStar_Range.dummyRange
                then
                  let uu____64505 =
                    FStar_Range.string_of_def_range
                      ps.FStar_Tactics_Types.entry_range
                     in
                  FStar_Util.format1 "Location: %s\n" uu____64505
                else ""  in
              let uu____64511 =
                let uu____64515 =
                  let uu____64517 =
                    FStar_TypeChecker_Env.debug
                      ps.FStar_Tactics_Types.main_context
                      (FStar_Options.Other "Imp")
                     in
                  if uu____64517
                  then
                    let uu____64522 =
                      FStar_Common.string_of_list p_imp
                        ps.FStar_Tactics_Types.all_implicits
                       in
                    FStar_Util.format1 "Imps: %s\n" uu____64522
                  else ""  in
                [uu____64515]  in
              uu____64501 :: uu____64511  in
            uu____64492 :: uu____64497  in
          let uu____64532 =
            let uu____64536 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "Goal"
                       (FStar_Pervasives_Native.Some
                          (((Prims.parse_int "1") + i), n1)) ps g)
                ps.FStar_Tactics_Types.goals
               in
            let uu____64556 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "SMT Goal"
                       (FStar_Pervasives_Native.Some
                          ((((Prims.parse_int "1") + n_active) + i), n1)) ps
                       g) ps.FStar_Tactics_Types.smt_goals
               in
            FStar_List.append uu____64536 uu____64556  in
          FStar_List.append uu____64488 uu____64532  in
        FStar_String.concat "" uu____64484
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      let uu____64586 =
        let uu____64587 = FStar_Tactics_Types.goal_env g  in
        FStar_TypeChecker_Env.all_binders uu____64587  in
      let uu____64588 =
        let uu____64593 =
          let uu____64594 = FStar_Tactics_Types.goal_env g  in
          FStar_TypeChecker_Env.dsenv uu____64594  in
        FStar_Syntax_Print.binders_to_json uu____64593  in
      FStar_All.pipe_right uu____64586 uu____64588  in
    let uu____64595 =
      let uu____64603 =
        let uu____64611 =
          let uu____64617 =
            let uu____64618 =
              let uu____64626 =
                let uu____64632 =
                  let uu____64633 =
                    let uu____64635 = FStar_Tactics_Types.goal_env g  in
                    let uu____64636 = FStar_Tactics_Types.goal_witness g  in
                    tts uu____64635 uu____64636  in
                  FStar_Util.JsonStr uu____64633  in
                ("witness", uu____64632)  in
              let uu____64639 =
                let uu____64647 =
                  let uu____64653 =
                    let uu____64654 =
                      let uu____64656 = FStar_Tactics_Types.goal_env g  in
                      let uu____64657 = FStar_Tactics_Types.goal_type g  in
                      tts uu____64656 uu____64657  in
                    FStar_Util.JsonStr uu____64654  in
                  ("type", uu____64653)  in
                [uu____64647;
                ("label", (FStar_Util.JsonStr (g.FStar_Tactics_Types.label)))]
                 in
              uu____64626 :: uu____64639  in
            FStar_Util.JsonAssoc uu____64618  in
          ("goal", uu____64617)  in
        [uu____64611]  in
      ("hyps", g_binders) :: uu____64603  in
    FStar_Util.JsonAssoc uu____64595
  
let (ps_to_json :
  (Prims.string * FStar_Tactics_Types.proofstate) -> FStar_Util.json) =
  fun uu____64711  ->
    match uu____64711 with
    | (msg,ps) ->
        let uu____64721 =
          let uu____64729 =
            let uu____64737 =
              let uu____64745 =
                let uu____64753 =
                  let uu____64759 =
                    let uu____64760 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____64760  in
                  ("goals", uu____64759)  in
                let uu____64765 =
                  let uu____64773 =
                    let uu____64779 =
                      let uu____64780 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____64780  in
                    ("smt-goals", uu____64779)  in
                  [uu____64773]  in
                uu____64753 :: uu____64765  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____64745
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____64737  in
          let uu____64814 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____64830 =
                let uu____64836 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____64836)  in
              [uu____64830]
            else []  in
          FStar_List.append uu____64729 uu____64814  in
        FStar_Util.JsonAssoc uu____64721
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____64876  ->
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
         (let uu____64907 = FStar_Tactics_Types.subst_proof_state subst1 ps
             in
          dump_proofstate uu____64907 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let traise : 'a . Prims.exn -> 'a tac =
  fun e  -> mk_tac (fun ps  -> FStar_Tactics_Result.Failed (e, ps)) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____64980 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____64980
          then dump_proofstate ps (Prims.op_Hat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed
           ((FStar_Tactics_Types.TacticFailure msg), ps))
  
let fail1 : 'Auu____64994 . Prims.string -> Prims.string -> 'Auu____64994 tac
  =
  fun msg  ->
    fun x  -> let uu____65011 = FStar_Util.format1 msg x  in fail uu____65011
  
let fail2 :
  'Auu____65022 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____65022 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        let uu____65046 = FStar_Util.format2 msg x y  in fail uu____65046
  
let fail3 :
  'Auu____65059 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____65059 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____65090 = FStar_Util.format3 msg x y z  in fail uu____65090
  
let fail4 :
  'Auu____65105 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____65105 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____65143 = FStar_Util.format4 msg x y z w  in
            fail uu____65143
  
let catch : 'a . 'a tac -> (Prims.exn,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____65178 = run t ps  in
         match uu____65178 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___802_65202 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___802_65202.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___802_65202.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___802_65202.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___802_65202.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___802_65202.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___802_65202.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___802_65202.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___802_65202.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___802_65202.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___802_65202.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___802_65202.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (uu___802_65202.FStar_Tactics_Types.local_state)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let recover : 'a . 'a tac -> (Prims.exn,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let uu____65241 = run t ps  in
         match uu____65241 with
         | FStar_Tactics_Result.Success (a,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inr a), q)
         | FStar_Tactics_Result.Failed (m,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inl m), q))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____65289 = catch t  in
    bind uu____65289
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____65316 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try
           (fun uu___828_65348  ->
              match () with
              | () -> let uu____65353 = trytac t  in run uu____65353 ps) ()
         with
         | FStar_Errors.Err (uu____65369,msg) ->
             (log ps
                (fun uu____65375  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____65381,msg,uu____65383) ->
             (log ps
                (fun uu____65388  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____65425 = run t ps  in
           match uu____65425 with
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
  fun p  -> mk_tac (fun uu____65449  -> FStar_Tactics_Result.Success ((), p)) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___863_65464 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___863_65464.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___863_65464.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___863_65464.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___863_65464.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___863_65464.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___863_65464.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___863_65464.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___863_65464.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___863_65464.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___863_65464.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___863_65464.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___863_65464.FStar_Tactics_Types.local_state)
            }))
  
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____65488 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____65488
         then
           let uu____65492 = FStar_Syntax_Print.term_to_string t1  in
           let uu____65494 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____65492
             uu____65494
         else ());
        (try
           (fun uu___871_65505  ->
              match () with
              | () ->
                  let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
                  ((let uu____65513 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____65513
                    then
                      let uu____65517 =
                        FStar_Common.string_of_option
                          (FStar_TypeChecker_Rel.guard_to_string env) res
                         in
                      let uu____65519 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____65521 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.print3
                        "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____65517
                        uu____65519 uu____65521
                    else ());
                   (match res with
                    | FStar_Pervasives_Native.None  -> ret false
                    | FStar_Pervasives_Native.Some g ->
                        let uu____65532 =
                          add_implicits g.FStar_TypeChecker_Env.implicits  in
                        bind uu____65532 (fun uu____65537  -> ret true)))) ()
         with
         | FStar_Errors.Err (uu____65547,msg) ->
             mlog
               (fun uu____65553  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____65556  -> ret false)
         | FStar_Errors.Error (uu____65559,msg,r) ->
             mlog
               (fun uu____65567  ->
                  let uu____65568 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____65568) (fun uu____65572  -> ret false))
  
let (compress_implicits : unit tac) =
  bind get
    (fun ps  ->
       let imps = ps.FStar_Tactics_Types.all_implicits  in
       let g =
         let uu___897_65586 = FStar_TypeChecker_Env.trivial_guard  in
         {
           FStar_TypeChecker_Env.guard_f =
             (uu___897_65586.FStar_TypeChecker_Env.guard_f);
           FStar_TypeChecker_Env.deferred =
             (uu___897_65586.FStar_TypeChecker_Env.deferred);
           FStar_TypeChecker_Env.univ_ineqs =
             (uu___897_65586.FStar_TypeChecker_Env.univ_ineqs);
           FStar_TypeChecker_Env.implicits = imps
         }  in
       let g1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g
          in
       let ps' =
         let uu___901_65589 = ps  in
         {
           FStar_Tactics_Types.main_context =
             (uu___901_65589.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___901_65589.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (g1.FStar_TypeChecker_Env.implicits);
           FStar_Tactics_Types.goals =
             (uu___901_65589.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___901_65589.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___901_65589.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___901_65589.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___901_65589.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___901_65589.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___901_65589.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___901_65589.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___901_65589.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___901_65589.FStar_Tactics_Types.local_state)
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
          (fun uu____65616  ->
             (let uu____65618 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____65618
              then
                (FStar_Options.push ();
                 (let uu____65623 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____65627 = __do_unify env t1 t2  in
              bind uu____65627
                (fun r  ->
                   (let uu____65638 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____65638 then FStar_Options.pop () else ());
                   ret r)))
  
let (remove_solved_goals : unit tac) =
  bind get
    (fun ps  ->
       let ps' =
         let uu___916_65652 = ps  in
         let uu____65653 =
           FStar_List.filter
             (fun g  ->
                let uu____65659 = check_goal_solved g  in
                FStar_Option.isNone uu____65659) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___916_65652.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___916_65652.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___916_65652.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____65653;
           FStar_Tactics_Types.smt_goals =
             (uu___916_65652.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___916_65652.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___916_65652.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___916_65652.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___916_65652.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___916_65652.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___916_65652.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___916_65652.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___916_65652.FStar_Tactics_Types.local_state)
         }  in
       set ps')
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____65677 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____65677 with
      | FStar_Pervasives_Native.Some uu____65682 ->
          let uu____65683 =
            let uu____65685 = goal_to_string_verbose goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____65685  in
          fail uu____65683
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____65706 = FStar_Tactics_Types.goal_env goal  in
      let uu____65707 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____65706 solution uu____65707
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____65714 =
         let uu___929_65715 = p  in
         let uu____65716 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___929_65715.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___929_65715.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___929_65715.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____65716;
           FStar_Tactics_Types.smt_goals =
             (uu___929_65715.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___929_65715.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___929_65715.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___929_65715.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___929_65715.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___929_65715.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___929_65715.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___929_65715.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___929_65715.FStar_Tactics_Types.local_state)
         }  in
       set uu____65714)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      mlog
        (fun uu____65738  ->
           let uu____65739 =
             let uu____65741 = FStar_Tactics_Types.goal_witness goal  in
             FStar_Syntax_Print.term_to_string uu____65741  in
           let uu____65742 = FStar_Syntax_Print.term_to_string solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____65739 uu____65742)
        (fun uu____65747  ->
           let uu____65748 = trysolve goal solution  in
           bind uu____65748
             (fun b  ->
                if b
                then bind __dismiss (fun uu____65760  -> remove_solved_goals)
                else
                  (let uu____65763 =
                     let uu____65765 =
                       let uu____65767 = FStar_Tactics_Types.goal_env goal
                          in
                       tts uu____65767 solution  in
                     let uu____65768 =
                       let uu____65770 = FStar_Tactics_Types.goal_env goal
                          in
                       let uu____65771 =
                         FStar_Tactics_Types.goal_witness goal  in
                       tts uu____65770 uu____65771  in
                     let uu____65772 =
                       let uu____65774 = FStar_Tactics_Types.goal_env goal
                          in
                       let uu____65775 = FStar_Tactics_Types.goal_type goal
                          in
                       tts uu____65774 uu____65775  in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____65765 uu____65768 uu____65772
                      in
                   fail uu____65763)))
  
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____65792 = set_solution goal solution  in
      bind uu____65792
        (fun uu____65796  ->
           bind __dismiss (fun uu____65798  -> remove_solved_goals))
  
let (set_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___945_65817 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___945_65817.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___945_65817.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___945_65817.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals = gs;
              FStar_Tactics_Types.smt_goals =
                (uu___945_65817.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___945_65817.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___945_65817.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___945_65817.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___945_65817.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___945_65817.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___945_65817.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___945_65817.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___945_65817.FStar_Tactics_Types.local_state)
            }))
  
let (set_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___949_65836 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___949_65836.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___949_65836.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___949_65836.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___949_65836.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals = gs;
              FStar_Tactics_Types.depth =
                (uu___949_65836.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___949_65836.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___949_65836.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___949_65836.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___949_65836.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___949_65836.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___949_65836.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___949_65836.FStar_Tactics_Types.local_state)
            }))
  
let (dismiss_all : unit tac) = set_goals [] 
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____65852 = FStar_Options.defensive ()  in
    if uu____65852
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____65862 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____65862)
         in
      let b2 =
        b1 &&
          (let uu____65866 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____65866)
         in
      let rec aux b3 e =
        let uu____65881 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____65881 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____65901 =
        (let uu____65905 = aux b2 env  in Prims.op_Negation uu____65905) &&
          (let uu____65908 = FStar_ST.op_Bang nwarn  in
           uu____65908 < (Prims.parse_int "5"))
         in
      (if uu____65901
       then
         ((let uu____65934 =
             let uu____65935 = FStar_Tactics_Types.goal_type g  in
             uu____65935.FStar_Syntax_Syntax.pos  in
           let uu____65938 =
             let uu____65944 =
               let uu____65946 = goal_to_string_verbose g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____65946
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____65944)  in
           FStar_Errors.log_issue uu____65934 uu____65938);
          (let uu____65950 =
             let uu____65952 = FStar_ST.op_Bang nwarn  in
             uu____65952 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____65950))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___971_66021 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___971_66021.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___971_66021.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___971_66021.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___971_66021.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___971_66021.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___971_66021.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___971_66021.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___971_66021.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___971_66021.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___971_66021.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___971_66021.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___971_66021.FStar_Tactics_Types.local_state)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___976_66042 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___976_66042.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___976_66042.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___976_66042.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___976_66042.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___976_66042.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___976_66042.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___976_66042.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___976_66042.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___976_66042.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___976_66042.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___976_66042.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___976_66042.FStar_Tactics_Types.local_state)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___981_66063 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___981_66063.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___981_66063.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___981_66063.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___981_66063.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___981_66063.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___981_66063.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___981_66063.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___981_66063.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___981_66063.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___981_66063.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___981_66063.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___981_66063.FStar_Tactics_Types.local_state)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___986_66084 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___986_66084.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___986_66084.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___986_66084.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___986_66084.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___986_66084.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___986_66084.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___986_66084.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___986_66084.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___986_66084.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___986_66084.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___986_66084.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___986_66084.FStar_Tactics_Types.local_state)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____66096  -> add_goals [g]) 
let (new_uvar :
  Prims.string ->
    env ->
      FStar_Reflection_Data.typ ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar) tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____66127 =
          FStar_TypeChecker_Env.new_implicit_var_aux reason
            typ.FStar_Syntax_Syntax.pos env typ
            FStar_Syntax_Syntax.Allow_untyped FStar_Pervasives_Native.None
           in
        match uu____66127 with
        | (u,ctx_uvar,g_u) ->
            let uu____66165 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____66165
              (fun uu____66174  ->
                 let uu____66175 =
                   let uu____66180 =
                     let uu____66181 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____66181  in
                   (u, uu____66180)  in
                 ret uu____66175)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____66202 = FStar_Syntax_Util.un_squash t1  in
    match uu____66202 with
    | FStar_Pervasives_Native.Some t' ->
        let t'1 = FStar_Syntax_Util.unascribe t'  in
        let uu____66214 =
          let uu____66215 = FStar_Syntax_Subst.compress t'1  in
          uu____66215.FStar_Syntax_Syntax.n  in
        (match uu____66214 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____66220 -> false)
    | uu____66222 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____66235 = FStar_Syntax_Util.un_squash t  in
    match uu____66235 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____66246 =
          let uu____66247 = FStar_Syntax_Subst.compress t'  in
          uu____66247.FStar_Syntax_Syntax.n  in
        (match uu____66246 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____66252 -> false)
    | uu____66254 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____66267  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____66279 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____66279 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____66286 = goal_to_string_verbose hd1  in
                    let uu____66288 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____66286 uu____66288);
                   ret hd1)))
  
let (tadmit_t : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____66301 =
      bind get
        (fun ps  ->
           let uu____66307 = cur_goal ()  in
           bind uu____66307
             (fun g  ->
                (let uu____66314 =
                   let uu____66315 = FStar_Tactics_Types.goal_type g  in
                   uu____66315.FStar_Syntax_Syntax.pos  in
                 let uu____66318 =
                   let uu____66324 =
                     let uu____66326 =
                       goal_to_string "" FStar_Pervasives_Native.None ps g
                        in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____66326
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____66324)  in
                 FStar_Errors.log_issue uu____66314 uu____66318);
                solve' g t))
       in
    FStar_All.pipe_left (wrap_err "tadmit_t") uu____66301
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____66349  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___1031_66360 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___1031_66360.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___1031_66360.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___1031_66360.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___1031_66360.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___1031_66360.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___1031_66360.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___1031_66360.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___1031_66360.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___1031_66360.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___1031_66360.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___1031_66360.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (uu___1031_66360.FStar_Tactics_Types.local_state)
           }  in
         let uu____66362 = set ps1  in
         bind uu____66362
           (fun uu____66367  ->
              let uu____66368 = FStar_BigInt.of_int_fs n1  in ret uu____66368))
  
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
              let uu____66406 = env.FStar_TypeChecker_Env.universe_of env phi
                 in
              FStar_Syntax_Util.mk_squash uu____66406 phi  in
            let uu____66407 = new_uvar reason env typ  in
            bind uu____66407
              (fun uu____66422  ->
                 match uu____66422 with
                 | (uu____66429,ctx_uvar) ->
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
             (fun uu____66476  ->
                let uu____66477 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____66477)
             (fun uu____66482  ->
                let e1 =
                  let uu___1049_66484 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1049_66484.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1049_66484.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1049_66484.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1049_66484.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1049_66484.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1049_66484.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1049_66484.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1049_66484.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1049_66484.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1049_66484.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1049_66484.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1049_66484.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1049_66484.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1049_66484.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1049_66484.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1049_66484.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1049_66484.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1049_66484.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1049_66484.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1049_66484.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1049_66484.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1049_66484.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1049_66484.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1049_66484.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1049_66484.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1049_66484.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1049_66484.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1049_66484.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1049_66484.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1049_66484.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1049_66484.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1049_66484.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1049_66484.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1049_66484.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1049_66484.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1049_66484.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1049_66484.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1049_66484.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1049_66484.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1049_66484.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1049_66484.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1049_66484.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___1053_66496  ->
                     match () with
                     | () ->
                         let uu____66505 =
                           FStar_TypeChecker_TcTerm.type_of_tot_term e1 t  in
                         ret uu____66505) ()
                with
                | FStar_Errors.Err (uu____66532,msg) ->
                    let uu____66536 = tts e1 t  in
                    let uu____66538 =
                      let uu____66540 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____66540
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____66536 uu____66538 msg
                | FStar_Errors.Error (uu____66550,msg,uu____66552) ->
                    let uu____66555 = tts e1 t  in
                    let uu____66557 =
                      let uu____66559 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____66559
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____66555 uu____66557 msg))
  
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
             (fun uu____66612  ->
                let uu____66613 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc_ghost(%s)\n" uu____66613)
             (fun uu____66618  ->
                let e1 =
                  let uu___1070_66620 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1070_66620.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1070_66620.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1070_66620.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1070_66620.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1070_66620.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1070_66620.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1070_66620.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1070_66620.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1070_66620.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1070_66620.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1070_66620.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1070_66620.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1070_66620.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1070_66620.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1070_66620.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1070_66620.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1070_66620.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1070_66620.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1070_66620.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1070_66620.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1070_66620.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1070_66620.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1070_66620.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1070_66620.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1070_66620.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1070_66620.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1070_66620.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1070_66620.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1070_66620.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1070_66620.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1070_66620.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1070_66620.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1070_66620.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1070_66620.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1070_66620.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1070_66620.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1070_66620.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1070_66620.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1070_66620.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1070_66620.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1070_66620.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1070_66620.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___1074_66635  ->
                     match () with
                     | () ->
                         let uu____66644 =
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e1 t
                            in
                         (match uu____66644 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____66682,msg) ->
                    let uu____66686 = tts e1 t  in
                    let uu____66688 =
                      let uu____66690 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____66690
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____66686 uu____66688 msg
                | FStar_Errors.Error (uu____66700,msg,uu____66702) ->
                    let uu____66705 = tts e1 t  in
                    let uu____66707 =
                      let uu____66709 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____66709
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____66705 uu____66707 msg))
  
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
             (fun uu____66762  ->
                let uu____66763 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____66763)
             (fun uu____66769  ->
                let e1 =
                  let uu___1095_66771 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1095_66771.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1095_66771.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1095_66771.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1095_66771.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1095_66771.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1095_66771.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1095_66771.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1095_66771.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1095_66771.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1095_66771.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1095_66771.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1095_66771.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1095_66771.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1095_66771.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1095_66771.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1095_66771.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1095_66771.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1095_66771.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1095_66771.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1095_66771.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1095_66771.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1095_66771.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1095_66771.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1095_66771.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1095_66771.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1095_66771.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1095_66771.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1095_66771.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1095_66771.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1095_66771.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1095_66771.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1095_66771.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1095_66771.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1095_66771.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1095_66771.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1095_66771.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1095_66771.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1095_66771.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1095_66771.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1095_66771.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1095_66771.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1095_66771.FStar_TypeChecker_Env.nbe)
                  }  in
                let e2 =
                  let uu___1098_66774 = e1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1098_66774.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1098_66774.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1098_66774.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1098_66774.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1098_66774.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1098_66774.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1098_66774.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1098_66774.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1098_66774.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1098_66774.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1098_66774.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1098_66774.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1098_66774.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1098_66774.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1098_66774.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1098_66774.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1098_66774.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1098_66774.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1098_66774.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1098_66774.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1098_66774.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1098_66774.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1098_66774.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1098_66774.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___1098_66774.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1098_66774.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1098_66774.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1098_66774.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1098_66774.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1098_66774.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1098_66774.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1098_66774.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1098_66774.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1098_66774.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1098_66774.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1098_66774.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1098_66774.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1098_66774.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1098_66774.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1098_66774.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1098_66774.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1098_66774.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___1102_66789  ->
                     match () with
                     | () ->
                         let uu____66798 =
                           FStar_TypeChecker_TcTerm.tc_term e2 t  in
                         (match uu____66798 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____66836,msg) ->
                    let uu____66840 = tts e2 t  in
                    let uu____66842 =
                      let uu____66844 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____66844
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____66840 uu____66842 msg
                | FStar_Errors.Error (uu____66854,msg,uu____66856) ->
                    let uu____66859 = tts e2 t  in
                    let uu____66861 =
                      let uu____66863 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____66863
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____66859 uu____66861 msg))
  
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
  fun uu____66897  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___1127_66916 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___1127_66916.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___1127_66916.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___1127_66916.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___1127_66916.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___1127_66916.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___1127_66916.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___1127_66916.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___1127_66916.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___1127_66916.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___1127_66916.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___1127_66916.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___1127_66916.FStar_Tactics_Types.local_state)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____66941 = get_guard_policy ()  in
      bind uu____66941
        (fun old_pol  ->
           let uu____66947 = set_guard_policy pol  in
           bind uu____66947
             (fun uu____66951  ->
                bind t
                  (fun r  ->
                     let uu____66955 = set_guard_policy old_pol  in
                     bind uu____66955 (fun uu____66959  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____66963 = let uu____66968 = cur_goal ()  in trytac uu____66968  in
  bind uu____66963
    (fun uu___609_66975  ->
       match uu___609_66975 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____66981 = FStar_Options.peek ()  in ret uu____66981)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        mlog
          (fun uu____67006  ->
             let uu____67007 = FStar_TypeChecker_Rel.guard_to_string e g  in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason
               uu____67007)
          (fun uu____67012  ->
             let uu____67013 =
               add_implicits g.FStar_TypeChecker_Env.implicits  in
             bind uu____67013
               (fun uu____67017  ->
                  bind getopts
                    (fun opts  ->
                       let uu____67021 =
                         let uu____67022 =
                           FStar_TypeChecker_Rel.simplify_guard e g  in
                         uu____67022.FStar_TypeChecker_Env.guard_f  in
                       match uu____67021 with
                       | FStar_TypeChecker_Common.Trivial  -> ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____67026 = istrivial e f  in
                           if uu____67026
                           then ret ()
                           else
                             bind get
                               (fun ps  ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop  ->
                                      ((let uu____67039 =
                                          let uu____67045 =
                                            let uu____67047 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g
                                               in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____67047
                                             in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____67045)
                                           in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____67039);
                                       ret ())
                                  | FStar_Tactics_Types.Goal  ->
                                      mlog
                                        (fun uu____67053  ->
                                           let uu____67054 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____67054)
                                        (fun uu____67059  ->
                                           let uu____67060 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____67060
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___1156_67068 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___1156_67068.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___1156_67068.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___1156_67068.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___1156_67068.FStar_Tactics_Types.label)
                                                  }  in
                                                push_goals [goal1]))
                                  | FStar_Tactics_Types.SMT  ->
                                      mlog
                                        (fun uu____67072  ->
                                           let uu____67073 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____67073)
                                        (fun uu____67078  ->
                                           let uu____67079 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____67079
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___1163_67087 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___1163_67087.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___1163_67087.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___1163_67087.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___1163_67087.FStar_Tactics_Types.label)
                                                  }  in
                                                push_smt_goals [goal1]))
                                  | FStar_Tactics_Types.Force  ->
                                      mlog
                                        (fun uu____67091  ->
                                           let uu____67092 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____67092)
                                        (fun uu____67096  ->
                                           try
                                             (fun uu___1170_67101  ->
                                                match () with
                                                | () ->
                                                    let uu____67104 =
                                                      let uu____67106 =
                                                        let uu____67108 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____67108
                                                         in
                                                      Prims.op_Negation
                                                        uu____67106
                                                       in
                                                    if uu____67104
                                                    then
                                                      mlog
                                                        (fun uu____67115  ->
                                                           let uu____67116 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g
                                                              in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____67116)
                                                        (fun uu____67120  ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else ret ()) ()
                                           with
                                           | uu___1169_67125 ->
                                               mlog
                                                 (fun uu____67130  ->
                                                    let uu____67131 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g
                                                       in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____67131)
                                                 (fun uu____67135  ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____67147 =
      let uu____67150 = cur_goal ()  in
      bind uu____67150
        (fun goal  ->
           let uu____67156 =
             let uu____67165 = FStar_Tactics_Types.goal_env goal  in
             __tc_lax uu____67165 t  in
           bind uu____67156
             (fun uu____67176  ->
                match uu____67176 with
                | (uu____67185,typ,uu____67187) -> ret typ))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____67147
  
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
            let uu____67227 = mk_irrelevant_goal reason env phi opts label1
               in
            bind uu____67227 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____67239  ->
    let uu____67242 = cur_goal ()  in
    bind uu____67242
      (fun goal  ->
         let uu____67248 =
           let uu____67250 = FStar_Tactics_Types.goal_env goal  in
           let uu____67251 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____67250 uu____67251  in
         if uu____67248
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____67257 =
              let uu____67259 = FStar_Tactics_Types.goal_env goal  in
              let uu____67260 = FStar_Tactics_Types.goal_type goal  in
              tts uu____67259 uu____67260  in
            fail1 "Not a trivial goal: %s" uu____67257))
  
let divide : 'a 'b . FStar_BigInt.t -> 'a tac -> 'b tac -> ('a * 'b) tac =
  fun n1  ->
    fun l  ->
      fun r  ->
        bind get
          (fun p  ->
             let uu____67311 =
               try
                 (fun uu___1226_67334  ->
                    match () with
                    | () ->
                        let uu____67345 =
                          let uu____67354 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____67354
                            p.FStar_Tactics_Types.goals
                           in
                        ret uu____67345) ()
               with | uu___1225_67365 -> fail "divide: not enough goals"  in
             bind uu____67311
               (fun uu____67402  ->
                  match uu____67402 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___1208_67428 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___1208_67428.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___1208_67428.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___1208_67428.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___1208_67428.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___1208_67428.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___1208_67428.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___1208_67428.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___1208_67428.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___1208_67428.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___1208_67428.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___1208_67428.FStar_Tactics_Types.local_state)
                        }  in
                      let uu____67429 = set lp  in
                      bind uu____67429
                        (fun uu____67437  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___1214_67453 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___1214_67453.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___1214_67453.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___1214_67453.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___1214_67453.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___1214_67453.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___1214_67453.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___1214_67453.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___1214_67453.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___1214_67453.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___1214_67453.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___1214_67453.FStar_Tactics_Types.local_state)
                                       }  in
                                     let uu____67454 = set rp  in
                                     bind uu____67454
                                       (fun uu____67462  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___1220_67478 =
                                                        rp'  in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___1220_67478.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___1220_67478.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___1220_67478.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___1220_67478.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___1220_67478.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___1220_67478.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___1220_67478.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___1220_67478.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___1220_67478.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___1220_67478.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___1220_67478.FStar_Tactics_Types.local_state)
                                                      }  in
                                                    let uu____67479 = set p'
                                                       in
                                                    bind uu____67479
                                                      (fun uu____67487  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____67493 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____67515 = divide FStar_BigInt.one f idtac  in
    bind uu____67515
      (fun uu____67528  -> match uu____67528 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____67566::uu____67567 ->
             let uu____67570 =
               let uu____67579 = map tau  in
               divide FStar_BigInt.one tau uu____67579  in
             bind uu____67570
               (fun uu____67597  ->
                  match uu____67597 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____67639 =
        bind t1
          (fun uu____67644  ->
             let uu____67645 = map t2  in
             bind uu____67645 (fun uu____67653  -> ret ()))
         in
      focus uu____67639
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____67663  ->
    let uu____67666 =
      let uu____67669 = cur_goal ()  in
      bind uu____67669
        (fun goal  ->
           let uu____67678 =
             let uu____67685 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____67685  in
           match uu____67678 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____67694 =
                 let uu____67696 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____67696  in
               if uu____67694
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____67705 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____67705 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____67719 = new_uvar "intro" env' typ'  in
                  bind uu____67719
                    (fun uu____67736  ->
                       match uu____67736 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c))
                              in
                           let uu____67760 = set_solution goal sol  in
                           bind uu____67760
                             (fun uu____67766  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                    goal.FStar_Tactics_Types.label
                                   in
                                let uu____67768 =
                                  let uu____67771 = bnorm_goal g  in
                                  replace_cur uu____67771  in
                                bind uu____67768 (fun uu____67773  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____67778 =
                 let uu____67780 = FStar_Tactics_Types.goal_env goal  in
                 let uu____67781 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____67780 uu____67781  in
               fail1 "goal is not an arrow (%s)" uu____67778)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____67666
  
let (intro_rec :
  unit -> (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder) tac) =
  fun uu____67799  ->
    let uu____67806 = cur_goal ()  in
    bind uu____67806
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____67825 =
            let uu____67832 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____67832  in
          match uu____67825 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____67845 =
                let uu____67847 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____67847  in
              if uu____67845
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____67864 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____67864
                    in
                 let bs =
                   let uu____67875 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____67875; b]  in
                 let env' =
                   let uu____67901 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____67901 bs  in
                 let uu____67902 =
                   let uu____67909 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____67909  in
                 bind uu____67902
                   (fun uu____67929  ->
                      match uu____67929 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____67943 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____67946 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____67943
                              FStar_Parser_Const.effect_Tot_lid uu____67946
                              [] FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____67964 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____67964 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____67986 =
                                   let uu____67987 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____67987.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____67986
                                  in
                               let uu____68003 = set_solution goal tm  in
                               bind uu____68003
                                 (fun uu____68012  ->
                                    let uu____68013 =
                                      let uu____68016 =
                                        bnorm_goal
                                          (let uu___1291_68019 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___1291_68019.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___1291_68019.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___1291_68019.FStar_Tactics_Types.is_guard);
                                             FStar_Tactics_Types.label =
                                               (uu___1291_68019.FStar_Tactics_Types.label)
                                           })
                                         in
                                      replace_cur uu____68016  in
                                    bind uu____68013
                                      (fun uu____68026  ->
                                         let uu____68027 =
                                           let uu____68032 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____68032, b)  in
                                         ret uu____68027)))))
          | FStar_Pervasives_Native.None  ->
              let uu____68041 =
                let uu____68043 = FStar_Tactics_Types.goal_env goal  in
                let uu____68044 = FStar_Tactics_Types.goal_type goal  in
                tts uu____68043 uu____68044  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____68041))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____68064 = cur_goal ()  in
    bind uu____68064
      (fun goal  ->
         mlog
           (fun uu____68071  ->
              let uu____68072 =
                let uu____68074 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____68074  in
              FStar_Util.print1 "norm: witness = %s\n" uu____68072)
           (fun uu____68080  ->
              let steps =
                let uu____68084 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____68084
                 in
              let t =
                let uu____68088 = FStar_Tactics_Types.goal_env goal  in
                let uu____68089 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____68088 uu____68089  in
              let uu____68090 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____68090))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____68115 =
          bind get
            (fun ps  ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
                 | g::uu____68123 -> g.FStar_Tactics_Types.opts
                 | uu____68126 -> FStar_Options.peek ()  in
               mlog
                 (fun uu____68131  ->
                    let uu____68132 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____68132)
                 (fun uu____68137  ->
                    let uu____68138 = __tc_lax e t  in
                    bind uu____68138
                      (fun uu____68159  ->
                         match uu____68159 with
                         | (t1,uu____68169,uu____68170) ->
                             let steps =
                               let uu____68174 =
                                 FStar_TypeChecker_Normalize.tr_norm_steps s
                                  in
                               FStar_List.append
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu____68174
                                in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1
                                in
                             mlog
                               (fun uu____68180  ->
                                  let uu____68181 =
                                    FStar_Syntax_Print.term_to_string t2  in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____68181)
                               (fun uu____68185  -> ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____68115
  
let (refine_intro : unit -> unit tac) =
  fun uu____68198  ->
    let uu____68201 =
      let uu____68204 = cur_goal ()  in
      bind uu____68204
        (fun g  ->
           let uu____68211 =
             let uu____68222 = FStar_Tactics_Types.goal_env g  in
             let uu____68223 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____68222
               uu____68223
              in
           match uu____68211 with
           | (uu____68226,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____68252 =
                 let uu____68257 =
                   let uu____68262 =
                     let uu____68263 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____68263]  in
                   FStar_Syntax_Subst.open_term uu____68262 phi  in
                 match uu____68257 with
                 | (bvs,phi1) ->
                     let uu____68288 =
                       let uu____68289 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____68289  in
                     (uu____68288, phi1)
                  in
               (match uu____68252 with
                | (bv1,phi1) ->
                    let uu____68308 =
                      let uu____68311 = FStar_Tactics_Types.goal_env g  in
                      let uu____68312 =
                        let uu____68313 =
                          let uu____68316 =
                            let uu____68317 =
                              let uu____68324 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____68324)  in
                            FStar_Syntax_Syntax.NT uu____68317  in
                          [uu____68316]  in
                        FStar_Syntax_Subst.subst uu____68313 phi1  in
                      mk_irrelevant_goal "refine_intro refinement"
                        uu____68311 uu____68312 g.FStar_Tactics_Types.opts
                        g.FStar_Tactics_Types.label
                       in
                    bind uu____68308
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____68333  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____68201
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____68356 = cur_goal ()  in
      bind uu____68356
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____68365 = FStar_Tactics_Types.goal_env goal  in
               let uu____68366 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____68365 uu____68366
             else FStar_Tactics_Types.goal_env goal  in
           let uu____68369 = __tc env t  in
           bind uu____68369
             (fun uu____68388  ->
                match uu____68388 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____68403  ->
                         let uu____68404 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____68406 =
                           let uu____68408 =
                             FStar_Tactics_Types.goal_env goal  in
                           FStar_TypeChecker_Rel.guard_to_string uu____68408
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____68404 uu____68406)
                      (fun uu____68412  ->
                         let uu____68413 =
                           let uu____68416 =
                             FStar_Tactics_Types.goal_env goal  in
                           proc_guard "__exact typing" uu____68416 guard  in
                         bind uu____68413
                           (fun uu____68419  ->
                              mlog
                                (fun uu____68423  ->
                                   let uu____68424 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____68426 =
                                     let uu____68428 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____68428
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____68424 uu____68426)
                                (fun uu____68432  ->
                                   let uu____68433 =
                                     let uu____68437 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____68438 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____68437 typ uu____68438  in
                                   bind uu____68433
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____68448 =
                                             let uu____68450 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____68450 t1  in
                                           let uu____68451 =
                                             let uu____68453 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____68453 typ  in
                                           let uu____68454 =
                                             let uu____68456 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____68457 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____68456 uu____68457  in
                                           let uu____68458 =
                                             let uu____68460 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____68461 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____68460 uu____68461  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____68448 uu____68451
                                             uu____68454 uu____68458)))))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun try_refine  ->
    fun set_expected_typ1  ->
      fun tm  ->
        let uu____68487 =
          mlog
            (fun uu____68492  ->
               let uu____68493 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____68493)
            (fun uu____68498  ->
               let uu____68499 =
                 let uu____68506 = __exact_now set_expected_typ1 tm  in
                 catch uu____68506  in
               bind uu____68499
                 (fun uu___611_68515  ->
                    match uu___611_68515 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        traise e
                    | FStar_Util.Inl e ->
                        mlog
                          (fun uu____68526  ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____68530  ->
                             let uu____68531 =
                               let uu____68538 =
                                 let uu____68541 =
                                   norm [FStar_Syntax_Embeddings.Delta]  in
                                 bind uu____68541
                                   (fun uu____68546  ->
                                      let uu____68547 = refine_intro ()  in
                                      bind uu____68547
                                        (fun uu____68551  ->
                                           __exact_now set_expected_typ1 tm))
                                  in
                               catch uu____68538  in
                             bind uu____68531
                               (fun uu___610_68558  ->
                                  match uu___610_68558 with
                                  | FStar_Util.Inr r ->
                                      mlog
                                        (fun uu____68567  ->
                                           FStar_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu____68570  -> ret ())
                                  | FStar_Util.Inl uu____68571 ->
                                      mlog
                                        (fun uu____68573  ->
                                           FStar_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu____68576  -> traise e)))))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____68487
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____68628 = f x  in
          bind uu____68628
            (fun y  ->
               let uu____68636 = mapM f xs  in
               bind uu____68636 (fun ys  -> ret (y :: ys)))
  
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
          let uu____68708 = do_unify e ty1 ty2  in
          bind uu____68708
            (fun uu___612_68722  ->
               if uu___612_68722
               then ret acc
               else
                 (let uu____68742 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____68742 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____68763 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____68765 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____68763
                        uu____68765
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____68782 =
                        let uu____68784 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____68784  in
                      if uu____68782
                      then fail "Codomain is effectful"
                      else
                        (let uu____68808 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____68808
                           (fun uu____68835  ->
                              match uu____68835 with
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
      let uu____68925 =
        mlog
          (fun uu____68930  ->
             let uu____68931 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_apply: tm = %s\n" uu____68931)
          (fun uu____68936  ->
             let uu____68937 = cur_goal ()  in
             bind uu____68937
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____68945 = __tc e tm  in
                  bind uu____68945
                    (fun uu____68966  ->
                       match uu____68966 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____68979 =
                             let uu____68990 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____68990  in
                           bind uu____68979
                             (fun uvs  ->
                                let fix_qual q =
                                  match q with
                                  | FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Meta uu____69028)
                                      ->
                                      FStar_Pervasives_Native.Some
                                        (FStar_Syntax_Syntax.Implicit false)
                                  | uu____69032 -> q  in
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____69055  ->
                                       fun w  ->
                                         match uu____69055 with
                                         | (uvt,q,uu____69073) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, (fix_qual q))]) uvs tm1
                                   in
                                let uvset =
                                  let uu____69105 =
                                    FStar_Syntax_Free.new_uv_set ()  in
                                  FStar_List.fold_right
                                    (fun uu____69122  ->
                                       fun s  ->
                                         match uu____69122 with
                                         | (uu____69134,uu____69135,uv) ->
                                             let uu____69137 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                in
                                             FStar_Util.set_union s
                                               uu____69137) uvs uu____69105
                                   in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset  in
                                let uu____69147 = solve' goal w  in
                                bind uu____69147
                                  (fun uu____69152  ->
                                     let uu____69153 =
                                       mapM
                                         (fun uu____69170  ->
                                            match uu____69170 with
                                            | (uvt,q,uv) ->
                                                let uu____69182 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                   in
                                                (match uu____69182 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____69187 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____69188 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv)
                                                        in
                                                     if uu____69188
                                                     then ret ()
                                                     else
                                                       (let uu____69195 =
                                                          let uu____69198 =
                                                            bnorm_goal
                                                              (let uu___1452_69201
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___1452_69201.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___1452_69201.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false;
                                                                 FStar_Tactics_Types.label
                                                                   =
                                                                   (uu___1452_69201.FStar_Tactics_Types.label)
                                                               })
                                                             in
                                                          [uu____69198]  in
                                                        add_goals uu____69195)))
                                         uvs
                                        in
                                     bind uu____69153
                                       (fun uu____69206  ->
                                          proc_guard "apply guard" e guard))))))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____68925
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____69234 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____69234
    then
      let uu____69243 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____69258 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____69311 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____69243 with
      | (pre,post) ->
          let post1 =
            let uu____69344 =
              let uu____69355 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____69355]  in
            FStar_Syntax_Util.mk_app post uu____69344  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____69386 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____69386
       then
         let uu____69395 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____69395
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
            let uu____69474 = f x e  in
            bind uu____69474 (fun e'  -> fold_left f e' xs1)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____69489 =
      let uu____69492 =
        bind get
          (fun ps  ->
             mlog
               (fun uu____69499  ->
                  let uu____69500 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____69500)
               (fun uu____69506  ->
                  let is_unit_t t =
                    let uu____69514 =
                      let uu____69515 = FStar_Syntax_Subst.compress t  in
                      uu____69515.FStar_Syntax_Syntax.n  in
                    match uu____69514 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____69521 -> false  in
                  let uu____69523 = cur_goal ()  in
                  bind uu____69523
                    (fun goal  ->
                       let uu____69529 =
                         let uu____69538 = FStar_Tactics_Types.goal_env goal
                            in
                         __tc uu____69538 tm  in
                       bind uu____69529
                         (fun uu____69553  ->
                            match uu____69553 with
                            | (tm1,t,guard) ->
                                let uu____69565 =
                                  FStar_Syntax_Util.arrow_formals_comp t  in
                                (match uu____69565 with
                                 | (bs,comp) ->
                                     let uu____69598 = lemma_or_sq comp  in
                                     (match uu____69598 with
                                      | FStar_Pervasives_Native.None  ->
                                          fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre,post) ->
                                          let uu____69618 =
                                            fold_left
                                              (fun uu____69680  ->
                                                 fun uu____69681  ->
                                                   match (uu____69680,
                                                           uu____69681)
                                                   with
                                                   | ((b,aq),(uvs,imps,subst1))
                                                       ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst1
                                                           b.FStar_Syntax_Syntax.sort
                                                          in
                                                       let uu____69832 =
                                                         is_unit_t b_t  in
                                                       if uu____69832
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
                                                         (let uu____69955 =
                                                            let uu____69962 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            new_uvar
                                                              "apply_lemma"
                                                              uu____69962 b_t
                                                             in
                                                          bind uu____69955
                                                            (fun uu____69993 
                                                               ->
                                                               match uu____69993
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
                                          bind uu____69618
                                            (fun uu____70179  ->
                                               match uu____70179 with
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
                                                   let uu____70267 =
                                                     let uu____70271 =
                                                       FStar_Tactics_Types.goal_env
                                                         goal
                                                        in
                                                     let uu____70272 =
                                                       FStar_Syntax_Util.mk_squash
                                                         FStar_Syntax_Syntax.U_zero
                                                         post1
                                                        in
                                                     let uu____70273 =
                                                       FStar_Tactics_Types.goal_type
                                                         goal
                                                        in
                                                     do_unify uu____70271
                                                       uu____70272
                                                       uu____70273
                                                      in
                                                   bind uu____70267
                                                     (fun b  ->
                                                        if
                                                          Prims.op_Negation b
                                                        then
                                                          let uu____70284 =
                                                            let uu____70286 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            tts uu____70286
                                                              tm1
                                                             in
                                                          let uu____70287 =
                                                            let uu____70289 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            let uu____70290 =
                                                              FStar_Syntax_Util.mk_squash
                                                                FStar_Syntax_Syntax.U_zero
                                                                post1
                                                               in
                                                            tts uu____70289
                                                              uu____70290
                                                             in
                                                          let uu____70291 =
                                                            let uu____70293 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            let uu____70294 =
                                                              FStar_Tactics_Types.goal_type
                                                                goal
                                                               in
                                                            tts uu____70293
                                                              uu____70294
                                                             in
                                                          fail3
                                                            "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                            uu____70284
                                                            uu____70287
                                                            uu____70291
                                                        else
                                                          (let uu____70298 =
                                                             solve' goal
                                                               FStar_Syntax_Util.exp_unit
                                                              in
                                                           bind uu____70298
                                                             (fun uu____70306
                                                                 ->
                                                                let is_free_uvar
                                                                  uv t1 =
                                                                  let free_uvars
                                                                    =
                                                                    let uu____70332
                                                                    =
                                                                    let uu____70335
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____70335
                                                                     in
                                                                    FStar_List.map
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____70332
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
                                                                    let uu____70371
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____70371)
                                                                    goals
                                                                   in
                                                                let checkone
                                                                  t1 goals =
                                                                  let uu____70388
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                  match uu____70388
                                                                  with
                                                                  | (hd1,uu____70407)
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____70434)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____70451
                                                                    -> false)
                                                                   in
                                                                let uu____70453
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
                                                                    let uu____70496
                                                                    = imp  in
                                                                    match uu____70496
                                                                    with
                                                                    | 
                                                                    (term,ctx_uvar)
                                                                    ->
                                                                    let uu____70507
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____70507
                                                                    with
                                                                    | 
                                                                    (hd1,uu____70529)
                                                                    ->
                                                                    let uu____70554
                                                                    =
                                                                    let uu____70555
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____70555.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____70554
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____70563)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___1562_70583
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___1562_70583.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___1562_70583.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___1562_70583.FStar_Tactics_Types.is_guard);
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___1562_70583.FStar_Tactics_Types.label)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____70586
                                                                    ->
                                                                    mlog
                                                                    (fun
                                                                    uu____70592
                                                                     ->
                                                                    let uu____70593
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                                                     in
                                                                    let uu____70595
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____70593
                                                                    uu____70595)
                                                                    (fun
                                                                    uu____70602
                                                                     ->
                                                                    let env =
                                                                    let uu___1567_70604
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___1567_70604.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1567_70604.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1567_70604.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___1567_70604.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1567_70604.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1567_70604.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1567_70604.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1567_70604.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___1567_70604.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___1567_70604.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___1567_70604.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1567_70604.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1567_70604.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1567_70604.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1567_70604.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1567_70604.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1567_70604.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1567_70604.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___1567_70604.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___1567_70604.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___1567_70604.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1567_70604.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1567_70604.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1567_70604.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1567_70604.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1567_70604.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1567_70604.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1567_70604.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1567_70604.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1567_70604.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1567_70604.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1567_70604.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1567_70604.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1567_70604.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___1567_70604.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1567_70604.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1567_70604.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___1567_70604.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1567_70604.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1567_70604.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1567_70604.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1567_70604.FStar_TypeChecker_Env.nbe)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let uu____70607
                                                                    =
                                                                    let uu____70610
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____70614
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
                                                                    let uu____70616
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____70614
                                                                    uu____70616
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____70622
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    uu____70610
                                                                    uu____70622
                                                                    g_typ  in
                                                                    bind
                                                                    uu____70607
                                                                    (fun
                                                                    uu____70626
                                                                     ->
                                                                    ret []))))))
                                                                   in
                                                                bind
                                                                  uu____70453
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
                                                                    let uu____70690
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____70690
                                                                    then
                                                                    let uu____70695
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____70695
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
                                                                    let uu____70710
                                                                    =
                                                                    let uu____70712
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____70712
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____70710)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____70713
                                                                    =
                                                                    let uu____70716
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____70716
                                                                    guard  in
                                                                    bind
                                                                    uu____70713
                                                                    (fun
                                                                    uu____70720
                                                                     ->
                                                                    let uu____70721
                                                                    =
                                                                    let uu____70724
                                                                    =
                                                                    let uu____70726
                                                                    =
                                                                    let uu____70728
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____70729
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____70728
                                                                    uu____70729
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____70726
                                                                     in
                                                                    if
                                                                    uu____70724
                                                                    then
                                                                    let uu____70733
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____70733
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    goal.FStar_Tactics_Types.label
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____70721
                                                                    (fun
                                                                    uu____70738
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2)))))))))))))
         in
      focus uu____69492  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____69489
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____70762 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____70762 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____70772::(e1,uu____70774)::(e2,uu____70776)::[])) when
        (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) ||
          (FStar_Ident.lid_equals l FStar_Parser_Const.c_eq2_lid)
        -> FStar_Pervasives_Native.Some (e1, e2)
    | uu____70837 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____70862 = destruct_eq' typ  in
    match uu____70862 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____70892 = FStar_Syntax_Util.un_squash typ  in
        (match uu____70892 with
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
        let uu____70961 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____70961 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', bv', [])
            else
              (let uu____71019 = aux e'  in
               FStar_Util.map_opt uu____71019
                 (fun uu____71050  ->
                    match uu____71050 with
                    | (e'',bv,bvs) -> (e'', bv, (bv' :: bvs))))
         in
      let uu____71076 = aux e  in
      FStar_Util.map_opt uu____71076
        (fun uu____71107  ->
           match uu____71107 with
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
          let uu____71181 =
            let uu____71192 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____71192  in
          FStar_Util.map_opt uu____71181
            (fun uu____71210  ->
               match uu____71210 with
               | (e0,b11,bvs) ->
                   let s1 bv =
                     let uu___1640_71232 = bv  in
                     let uu____71233 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___1640_71232.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___1640_71232.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____71233
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___1644_71241 =
                       g.FStar_Tactics_Types.goal_ctx_uvar  in
                     let uu____71242 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____71251 =
                       let uu____71254 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____71254  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___1644_71241.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____71242;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____71251;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___1644_71241.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___1644_71241.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___1644_71241.FStar_Syntax_Syntax.ctx_uvar_range);
                       FStar_Syntax_Syntax.ctx_uvar_meta =
                         (uu___1644_71241.FStar_Syntax_Syntax.ctx_uvar_meta)
                     }  in
                   let uu___1647_71255 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1647_71255.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___1647_71255.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___1647_71255.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1647_71255.FStar_Tactics_Types.label)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____71266 =
      let uu____71269 = cur_goal ()  in
      bind uu____71269
        (fun goal  ->
           let uu____71277 = h  in
           match uu____71277 with
           | (bv,uu____71281) ->
               mlog
                 (fun uu____71289  ->
                    let uu____71290 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____71292 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____71290
                      uu____71292)
                 (fun uu____71297  ->
                    let uu____71298 =
                      let uu____71309 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____71309  in
                    match uu____71298 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                        let uu____71336 =
                          destruct_eq bv1.FStar_Syntax_Syntax.sort  in
                        (match uu____71336 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____71351 =
                               let uu____71352 =
                                 FStar_Syntax_Subst.compress x  in
                               uu____71352.FStar_Syntax_Syntax.n  in
                             (match uu____71351 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv2 =
                                    let uu___1670_71369 = bv2  in
                                    let uu____71370 =
                                      FStar_Syntax_Subst.subst s
                                        bv2.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1670_71369.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1670_71369.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____71370
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv1 :: bvs1)  in
                                  let new_goal =
                                    let uu___1674_71378 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____71379 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____71388 =
                                      let uu____71391 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____71391
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___1674_71378.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____71379;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____71388;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___1674_71378.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___1674_71378.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___1674_71378.FStar_Syntax_Syntax.ctx_uvar_range);
                                      FStar_Syntax_Syntax.ctx_uvar_meta =
                                        (uu___1674_71378.FStar_Syntax_Syntax.ctx_uvar_meta)
                                    }  in
                                  replace_cur
                                    (let uu___1677_71394 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___1677_71394.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___1677_71394.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___1677_71394.FStar_Tactics_Types.is_guard);
                                       FStar_Tactics_Types.label =
                                         (uu___1677_71394.FStar_Tactics_Types.label)
                                     })
                              | uu____71395 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____71397 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____71266
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____71427 =
        let uu____71430 = cur_goal ()  in
        bind uu____71430
          (fun goal  ->
             let uu____71441 = b  in
             match uu____71441 with
             | (bv,uu____71445) ->
                 let bv' =
                   let uu____71451 =
                     let uu___1688_71452 = bv  in
                     let uu____71453 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____71453;
                       FStar_Syntax_Syntax.index =
                         (uu___1688_71452.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___1688_71452.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____71451  in
                 let s1 =
                   let uu____71458 =
                     let uu____71459 =
                       let uu____71466 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____71466)  in
                     FStar_Syntax_Syntax.NT uu____71459  in
                   [uu____71458]  in
                 let uu____71471 = subst_goal bv bv' s1 goal  in
                 (match uu____71471 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____71427
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____71493 =
      let uu____71496 = cur_goal ()  in
      bind uu____71496
        (fun goal  ->
           let uu____71505 = b  in
           match uu____71505 with
           | (bv,uu____71509) ->
               let uu____71514 =
                 let uu____71525 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____71525  in
               (match uu____71514 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                    let uu____71552 = FStar_Syntax_Util.type_u ()  in
                    (match uu____71552 with
                     | (ty,u) ->
                         let uu____71561 = new_uvar "binder_retype" e0 ty  in
                         bind uu____71561
                           (fun uu____71580  ->
                              match uu____71580 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___1712_71590 = bv1  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1712_71590.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1712_71590.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____71594 =
                                      let uu____71595 =
                                        let uu____71602 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv1, uu____71602)  in
                                      FStar_Syntax_Syntax.NT uu____71595  in
                                    [uu____71594]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___1717_71614 = b1  in
                                         let uu____71615 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___1717_71614.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___1717_71614.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____71615
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____71622  ->
                                       let new_goal =
                                         let uu____71624 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____71625 =
                                           let uu____71626 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____71626
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____71624 uu____71625
                                          in
                                       let uu____71627 = add_goals [new_goal]
                                          in
                                       bind uu____71627
                                         (fun uu____71632  ->
                                            let uu____71633 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv1.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____71633
                                              goal.FStar_Tactics_Types.opts
                                              goal.FStar_Tactics_Types.label))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____71493
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____71659 =
        let uu____71662 = cur_goal ()  in
        bind uu____71662
          (fun goal  ->
             let uu____71671 = b  in
             match uu____71671 with
             | (bv,uu____71675) ->
                 let uu____71680 =
                   let uu____71691 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____71691  in
                 (match uu____71680 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                      let steps =
                        let uu____71721 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____71721
                         in
                      let sort' =
                        normalize steps e0 bv1.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___1738_71726 = bv1  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___1738_71726.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___1738_71726.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____71728 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____71728))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____71659
  
let (revert : unit -> unit tac) =
  fun uu____71741  ->
    let uu____71744 = cur_goal ()  in
    bind uu____71744
      (fun goal  ->
         let uu____71750 =
           let uu____71757 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____71757  in
         match uu____71750 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____71774 =
                 let uu____71777 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____71777  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____71774
                in
             let uu____71792 = new_uvar "revert" env' typ'  in
             bind uu____71792
               (fun uu____71808  ->
                  match uu____71808 with
                  | (r,u_r) ->
                      let uu____71817 =
                        let uu____71820 =
                          let uu____71821 =
                            let uu____71822 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____71822.FStar_Syntax_Syntax.pos  in
                          let uu____71825 =
                            let uu____71830 =
                              let uu____71831 =
                                let uu____71840 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____71840  in
                              [uu____71831]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____71830  in
                          uu____71825 FStar_Pervasives_Native.None
                            uu____71821
                           in
                        set_solution goal uu____71820  in
                      bind uu____71817
                        (fun uu____71859  ->
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
      let uu____71873 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____71873
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____71889 = cur_goal ()  in
    bind uu____71889
      (fun goal  ->
         mlog
           (fun uu____71897  ->
              let uu____71898 = FStar_Syntax_Print.binder_to_string b  in
              let uu____71900 =
                let uu____71902 =
                  let uu____71904 =
                    let uu____71913 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____71913  in
                  FStar_All.pipe_right uu____71904 FStar_List.length  in
                FStar_All.pipe_right uu____71902 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____71898 uu____71900)
           (fun uu____71934  ->
              let uu____71935 =
                let uu____71946 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____71946  in
              match uu____71935 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bv1,bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____71991 =
                          free_in bv1 bv'.FStar_Syntax_Syntax.sort  in
                        if uu____71991
                        then
                          let uu____71996 =
                            let uu____71998 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____71998
                             in
                          fail uu____71996
                        else check1 bvs2
                     in
                  let uu____72003 =
                    let uu____72005 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv1 uu____72005  in
                  if uu____72003
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____72012 = check1 bvs  in
                     bind uu____72012
                       (fun uu____72018  ->
                          let env' = push_bvs e' bvs  in
                          let uu____72020 =
                            let uu____72027 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____72027  in
                          bind uu____72020
                            (fun uu____72037  ->
                               match uu____72037 with
                               | (ut,uvar_ut) ->
                                   let uu____72046 = set_solution goal ut  in
                                   bind uu____72046
                                     (fun uu____72051  ->
                                        let uu____72052 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                            goal.FStar_Tactics_Types.label
                                           in
                                        replace_cur uu____72052))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____72060  ->
    let uu____72063 = cur_goal ()  in
    bind uu____72063
      (fun goal  ->
         let uu____72069 =
           let uu____72076 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____72076  in
         match uu____72069 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____72085) ->
             let uu____72090 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____72090)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____72103 = cur_goal ()  in
    bind uu____72103
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____72113 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____72113  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____72116  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____72129 = cur_goal ()  in
    bind uu____72129
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____72139 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____72139  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____72142  -> add_goals [g']))
  
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
            let uu____72183 = FStar_Syntax_Subst.compress t  in
            uu____72183.FStar_Syntax_Syntax.n  in
          let uu____72186 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___1922_72193 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___1922_72193.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___1922_72193.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____72186
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____72210 =
                   let uu____72211 = FStar_Syntax_Subst.compress t1  in
                   uu____72211.FStar_Syntax_Syntax.n  in
                 match uu____72210 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____72242 = ff hd1  in
                     bind uu____72242
                       (fun hd2  ->
                          let fa uu____72268 =
                            match uu____72268 with
                            | (a,q) ->
                                let uu____72289 = ff a  in
                                bind uu____72289 (fun a1  -> ret (a1, q))
                             in
                          let uu____72308 = mapM fa args  in
                          bind uu____72308
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____72390 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____72390 with
                      | (bs1,t') ->
                          let uu____72399 =
                            let uu____72402 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____72402 t'  in
                          bind uu____72399
                            (fun t''  ->
                               let uu____72406 =
                                 let uu____72407 =
                                   let uu____72426 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____72435 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____72426, uu____72435, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____72407  in
                               ret uu____72406))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____72510 = ff hd1  in
                     bind uu____72510
                       (fun hd2  ->
                          let ffb br =
                            let uu____72525 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____72525 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____72557 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____72557  in
                                let uu____72558 = ff1 e  in
                                bind uu____72558
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____72573 = mapM ffb brs  in
                          bind uu____72573
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____72617;
                          FStar_Syntax_Syntax.lbtyp = uu____72618;
                          FStar_Syntax_Syntax.lbeff = uu____72619;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____72621;
                          FStar_Syntax_Syntax.lbpos = uu____72622;_}::[]),e)
                     ->
                     let lb =
                       let uu____72650 =
                         let uu____72651 = FStar_Syntax_Subst.compress t1  in
                         uu____72651.FStar_Syntax_Syntax.n  in
                       match uu____72650 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____72655) -> lb
                       | uu____72671 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____72681 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____72681
                         (fun def1  ->
                            ret
                              (let uu___1875_72687 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1875_72687.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1875_72687.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1875_72687.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1875_72687.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1875_72687.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1875_72687.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____72688 = fflb lb  in
                     bind uu____72688
                       (fun lb1  ->
                          let uu____72698 =
                            let uu____72703 =
                              let uu____72704 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____72704]  in
                            FStar_Syntax_Subst.open_term uu____72703 e  in
                          match uu____72698 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____72734 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____72734  in
                              let uu____72735 = ff1 e1  in
                              bind uu____72735
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____72782 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____72782
                         (fun def  ->
                            ret
                              (let uu___1893_72788 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1893_72788.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1893_72788.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1893_72788.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1893_72788.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1893_72788.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1893_72788.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____72789 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____72789 with
                      | (lbs1,e1) ->
                          let uu____72804 = mapM fflb lbs1  in
                          bind uu____72804
                            (fun lbs2  ->
                               let uu____72816 = ff e1  in
                               bind uu____72816
                                 (fun e2  ->
                                    let uu____72824 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____72824 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____72895 = ff t2  in
                     bind uu____72895
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____72926 = ff t2  in
                     bind uu____72926
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____72933 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___1917_72940 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___1917_72940.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___1917_72940.FStar_Syntax_Syntax.vars)
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
              let uu____72987 =
                FStar_TypeChecker_TcTerm.tc_term
                  (let uu___1930_72996 = env  in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___1930_72996.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___1930_72996.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___1930_72996.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___1930_72996.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_sig =
                       (uu___1930_72996.FStar_TypeChecker_Env.gamma_sig);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___1930_72996.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___1930_72996.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___1930_72996.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___1930_72996.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.attrtab =
                       (uu___1930_72996.FStar_TypeChecker_Env.attrtab);
                     FStar_TypeChecker_Env.is_pattern =
                       (uu___1930_72996.FStar_TypeChecker_Env.is_pattern);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___1930_72996.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___1930_72996.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___1930_72996.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___1930_72996.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___1930_72996.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___1930_72996.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___1930_72996.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___1930_72996.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___1930_72996.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax = true;
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___1930_72996.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.phase1 =
                       (uu___1930_72996.FStar_TypeChecker_Env.phase1);
                     FStar_TypeChecker_Env.failhard =
                       (uu___1930_72996.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___1930_72996.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.uvar_subtyping =
                       (uu___1930_72996.FStar_TypeChecker_Env.uvar_subtyping);
                     FStar_TypeChecker_Env.tc_term =
                       (uu___1930_72996.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.type_of =
                       (uu___1930_72996.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___1930_72996.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.check_type_of =
                       (uu___1930_72996.FStar_TypeChecker_Env.check_type_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___1930_72996.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (uu___1930_72996.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (uu___1930_72996.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.fv_delta_depths =
                       (uu___1930_72996.FStar_TypeChecker_Env.fv_delta_depths);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___1930_72996.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (uu___1930_72996.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.splice =
                       (uu___1930_72996.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.postprocess =
                       (uu___1930_72996.FStar_TypeChecker_Env.postprocess);
                     FStar_TypeChecker_Env.is_native_tactic =
                       (uu___1930_72996.FStar_TypeChecker_Env.is_native_tactic);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___1930_72996.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (uu___1930_72996.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (uu___1930_72996.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.nbe =
                       (uu___1930_72996.FStar_TypeChecker_Env.nbe)
                   }) t
                 in
              match uu____72987 with
              | (t1,lcomp,g) ->
                  let uu____73003 =
                    (let uu____73007 =
                       FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                     Prims.op_Negation uu____73007) ||
                      (let uu____73010 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____73010)
                     in
                  if uu____73003
                  then ret t1
                  else
                    (let rewrite_eq =
                       let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                       let uu____73021 = new_uvar "pointwise_rec" env typ  in
                       bind uu____73021
                         (fun uu____73038  ->
                            match uu____73038 with
                            | (ut,uvar_ut) ->
                                (log ps
                                   (fun uu____73051  ->
                                      let uu____73052 =
                                        FStar_Syntax_Print.term_to_string t1
                                         in
                                      let uu____73054 =
                                        FStar_Syntax_Print.term_to_string ut
                                         in
                                      FStar_Util.print2
                                        "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                        uu____73052 uu____73054);
                                 (let uu____73057 =
                                    let uu____73060 =
                                      let uu____73061 =
                                        FStar_TypeChecker_TcTerm.universe_of
                                          env typ
                                         in
                                      FStar_Syntax_Util.mk_eq2 uu____73061
                                        typ t1 ut
                                       in
                                    add_irrelevant_goal
                                      "pointwise_rec equation" env
                                      uu____73060 opts label1
                                     in
                                  bind uu____73057
                                    (fun uu____73065  ->
                                       let uu____73066 =
                                         bind tau
                                           (fun uu____73072  ->
                                              let ut1 =
                                                FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                  env ut
                                                 in
                                              log ps
                                                (fun uu____73078  ->
                                                   let uu____73079 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1
                                                      in
                                                   let uu____73081 =
                                                     FStar_Syntax_Print.term_to_string
                                                       ut1
                                                      in
                                                   FStar_Util.print2
                                                     "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                     uu____73079 uu____73081);
                                              ret ut1)
                                          in
                                       focus uu____73066))))
                        in
                     let uu____73084 = catch rewrite_eq  in
                     bind uu____73084
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
          let uu____73296 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____73296
            (fun t1  ->
               let uu____73304 =
                 f env
                   (let uu___2007_73312 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___2007_73312.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___2007_73312.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____73304
                 (fun uu____73328  ->
                    match uu____73328 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____73351 =
                               let uu____73352 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____73352.FStar_Syntax_Syntax.n  in
                             match uu____73351 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____73389 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____73389
                                   (fun uu____73411  ->
                                      match uu____73411 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____73427 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____73427
                                            (fun uu____73451  ->
                                               match uu____73451 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___1987_73481 =
                                                         t3  in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___1987_73481.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___1987_73481.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____73523 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____73523 with
                                  | (bs1,t') ->
                                      let uu____73538 =
                                        let uu____73545 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____73545 ctrl1 t'
                                         in
                                      bind uu____73538
                                        (fun uu____73560  ->
                                           match uu____73560 with
                                           | (t'',ctrl2) ->
                                               let uu____73575 =
                                                 let uu____73582 =
                                                   let uu___2000_73585 = t4
                                                      in
                                                   let uu____73588 =
                                                     let uu____73589 =
                                                       let uu____73608 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____73617 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____73608,
                                                         uu____73617, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____73589
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____73588;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___2000_73585.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___2000_73585.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____73582, ctrl2)  in
                                               ret uu____73575))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____73670 -> ret (t3, ctrl1))))

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
              let uu____73716 = ctrl_tac_fold f env ctrl t  in
              bind uu____73716
                (fun uu____73737  ->
                   match uu____73737 with
                   | (t1,ctrl1) ->
                       let uu____73752 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____73752
                         (fun uu____73776  ->
                            match uu____73776 with
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
                let uu____73867 =
                  let uu____73875 =
                    add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                      opts label1
                     in
                  bind uu____73875
                    (fun uu____73886  ->
                       let uu____73887 = ctrl t1  in
                       bind uu____73887
                         (fun res  ->
                            let uu____73913 = trivial ()  in
                            bind uu____73913 (fun uu____73922  -> ret res)))
                   in
                bind uu____73867
                  (fun uu____73940  ->
                     match uu____73940 with
                     | (should_rewrite,ctrl1) ->
                         if Prims.op_Negation should_rewrite
                         then ret (t1, ctrl1)
                         else
                           (let uu____73969 =
                              FStar_TypeChecker_TcTerm.tc_term
                                (let uu___2037_73978 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___2037_73978.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___2037_73978.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___2037_73978.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___2037_73978.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___2037_73978.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___2037_73978.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___2037_73978.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___2037_73978.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___2037_73978.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___2037_73978.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___2037_73978.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___2037_73978.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___2037_73978.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___2037_73978.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___2037_73978.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___2037_73978.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___2037_73978.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___2037_73978.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___2037_73978.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___2037_73978.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___2037_73978.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___2037_73978.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___2037_73978.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___2037_73978.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___2037_73978.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___2037_73978.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___2037_73978.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___2037_73978.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___2037_73978.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___2037_73978.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___2037_73978.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___2037_73978.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___2037_73978.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___2037_73978.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___2037_73978.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___2037_73978.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___2037_73978.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___2037_73978.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___2037_73978.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___2037_73978.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___2037_73978.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___2037_73978.FStar_TypeChecker_Env.nbe)
                                 }) t1
                               in
                            match uu____73969 with
                            | (t2,lcomp,g) ->
                                let uu____73989 =
                                  (let uu____73993 =
                                     FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                       lcomp
                                      in
                                   Prims.op_Negation uu____73993) ||
                                    (let uu____73996 =
                                       FStar_TypeChecker_Env.is_trivial g  in
                                     Prims.op_Negation uu____73996)
                                   in
                                if uu____73989
                                then ret (t2, globalStop)
                                else
                                  (let typ =
                                     lcomp.FStar_Syntax_Syntax.res_typ  in
                                   let uu____74012 =
                                     new_uvar "pointwise_rec" env typ  in
                                   bind uu____74012
                                     (fun uu____74033  ->
                                        match uu____74033 with
                                        | (ut,uvar_ut) ->
                                            (log ps
                                               (fun uu____74050  ->
                                                  let uu____74051 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t2
                                                     in
                                                  let uu____74053 =
                                                    FStar_Syntax_Print.term_to_string
                                                      ut
                                                     in
                                                  FStar_Util.print2
                                                    "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                    uu____74051 uu____74053);
                                             (let uu____74056 =
                                                let uu____74059 =
                                                  let uu____74060 =
                                                    FStar_TypeChecker_TcTerm.universe_of
                                                      env typ
                                                     in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____74060 typ t2 ut
                                                   in
                                                add_irrelevant_goal
                                                  "rewrite_rec equation" env
                                                  uu____74059 opts label1
                                                 in
                                              bind uu____74056
                                                (fun uu____74068  ->
                                                   let uu____74069 =
                                                     bind rewriter
                                                       (fun uu____74083  ->
                                                          let ut1 =
                                                            FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                              env ut
                                                             in
                                                          log ps
                                                            (fun uu____74089 
                                                               ->
                                                               let uu____74090
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   t2
                                                                  in
                                                               let uu____74092
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   ut1
                                                                  in
                                                               FStar_Util.print2
                                                                 "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                                 uu____74090
                                                                 uu____74092);
                                                          ret (ut1, ctrl1))
                                                      in
                                                   focus uu____74069)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term -> (Prims.bool * FStar_BigInt.t) tac) ->
    unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____74137 =
        bind get
          (fun ps  ->
             let uu____74147 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____74147 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____74185  ->
                       let uu____74186 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____74186);
                  bind dismiss_all
                    (fun uu____74191  ->
                       let uu____74192 =
                         let uu____74199 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____74199
                           keepGoing gt1
                          in
                       bind uu____74192
                         (fun uu____74209  ->
                            match uu____74209 with
                            | (gt',uu____74217) ->
                                (log ps
                                   (fun uu____74221  ->
                                      let uu____74222 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____74222);
                                 (let uu____74225 = push_goals gs  in
                                  bind uu____74225
                                    (fun uu____74230  ->
                                       let uu____74231 =
                                         let uu____74234 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____74234]  in
                                       add_goals uu____74231)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____74137
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____74259 =
        bind get
          (fun ps  ->
             let uu____74269 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____74269 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____74307  ->
                       let uu____74308 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____74308);
                  bind dismiss_all
                    (fun uu____74313  ->
                       let uu____74314 =
                         let uu____74317 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____74317 gt1
                          in
                       bind uu____74314
                         (fun gt'  ->
                            log ps
                              (fun uu____74325  ->
                                 let uu____74326 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____74326);
                            (let uu____74329 = push_goals gs  in
                             bind uu____74329
                               (fun uu____74334  ->
                                  let uu____74335 =
                                    let uu____74338 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____74338]  in
                                  add_goals uu____74335))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____74259
  
let (trefl : unit -> unit tac) =
  fun uu____74351  ->
    let uu____74354 =
      let uu____74357 = cur_goal ()  in
      bind uu____74357
        (fun g  ->
           let uu____74375 =
             let uu____74380 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____74380  in
           match uu____74375 with
           | FStar_Pervasives_Native.Some t ->
               let uu____74388 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____74388 with
                | (hd1,args) ->
                    let uu____74427 =
                      let uu____74440 =
                        let uu____74441 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____74441.FStar_Syntax_Syntax.n  in
                      (uu____74440, args)  in
                    (match uu____74427 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____74455::(l,uu____74457)::(r,uu____74459)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____74506 =
                           let uu____74510 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____74510 l r  in
                         bind uu____74506
                           (fun b  ->
                              if b
                              then solve' g FStar_Syntax_Util.exp_unit
                              else
                                (let l1 =
                                   let uu____74521 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____74521 l
                                    in
                                 let r1 =
                                   let uu____74523 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____74523 r
                                    in
                                 let uu____74524 =
                                   let uu____74528 =
                                     FStar_Tactics_Types.goal_env g  in
                                   do_unify uu____74528 l1 r1  in
                                 bind uu____74524
                                   (fun b1  ->
                                      if b1
                                      then
                                        solve' g FStar_Syntax_Util.exp_unit
                                      else
                                        (let uu____74538 =
                                           let uu____74540 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____74540 l1  in
                                         let uu____74541 =
                                           let uu____74543 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____74543 r1  in
                                         fail2
                                           "not a trivial equality ((%s) vs (%s))"
                                           uu____74538 uu____74541))))
                     | (hd2,uu____74546) ->
                         let uu____74563 =
                           let uu____74565 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____74565 t  in
                         fail1 "trefl: not an equality (%s)" uu____74563))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____74354
  
let (dup : unit -> unit tac) =
  fun uu____74582  ->
    let uu____74585 = cur_goal ()  in
    bind uu____74585
      (fun g  ->
         let uu____74591 =
           let uu____74598 = FStar_Tactics_Types.goal_env g  in
           let uu____74599 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____74598 uu____74599  in
         bind uu____74591
           (fun uu____74609  ->
              match uu____74609 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___2129_74619 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___2129_74619.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___2129_74619.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___2129_74619.FStar_Tactics_Types.is_guard);
                      FStar_Tactics_Types.label =
                        (uu___2129_74619.FStar_Tactics_Types.label)
                    }  in
                  bind __dismiss
                    (fun uu____74622  ->
                       let uu____74623 =
                         let uu____74626 = FStar_Tactics_Types.goal_env g  in
                         let uu____74627 =
                           let uu____74628 =
                             let uu____74629 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____74630 =
                               FStar_Tactics_Types.goal_type g  in
                             FStar_TypeChecker_TcTerm.universe_of uu____74629
                               uu____74630
                              in
                           let uu____74631 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____74632 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____74628 uu____74631 u
                             uu____74632
                            in
                         add_irrelevant_goal "dup equation" uu____74626
                           uu____74627 g.FStar_Tactics_Types.opts
                           g.FStar_Tactics_Types.label
                          in
                       bind uu____74623
                         (fun uu____74636  ->
                            let uu____74637 = add_goals [g']  in
                            bind uu____74637 (fun uu____74641  -> ret ())))))
  
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
              let uu____74767 = f x y  in
              if uu____74767 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____74790 -> (acc, l11, l21)  in
        let uu____74805 = aux [] l1 l2  in
        match uu____74805 with | (pr,t1,t2) -> ((FStar_List.rev pr), t1, t2)
  
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
      let uu____74911 = get_phi g1  in
      match uu____74911 with
      | FStar_Pervasives_Native.None  -> fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____74918 = get_phi g2  in
          (match uu____74918 with
           | FStar_Pervasives_Native.None  -> fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let uu____74931 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2)
                  in
               (match uu____74931 with
                | (gamma,r1,r2) ->
                    let t1 =
                      let uu____74962 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1)
                         in
                      close_forall_no_univs1 uu____74962 phi1  in
                    let t2 =
                      let uu____74972 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2)
                         in
                      close_forall_no_univs1 uu____74972 phi2  in
                    let uu____74981 =
                      set_solution g1 FStar_Syntax_Util.exp_unit  in
                    bind uu____74981
                      (fun uu____74986  ->
                         let uu____74987 =
                           set_solution g2 FStar_Syntax_Util.exp_unit  in
                         bind uu____74987
                           (fun uu____74994  ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2  in
                              let nenv =
                                let uu___2180_74999 =
                                  FStar_Tactics_Types.goal_env g1  in
                                let uu____75000 =
                                  FStar_Util.smap_create
                                    (Prims.parse_int "100")
                                   in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___2180_74999.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___2180_74999.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___2180_74999.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___2180_74999.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____75000;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___2180_74999.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___2180_74999.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___2180_74999.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___2180_74999.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___2180_74999.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___2180_74999.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___2180_74999.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___2180_74999.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___2180_74999.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___2180_74999.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___2180_74999.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___2180_74999.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___2180_74999.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___2180_74999.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___2180_74999.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___2180_74999.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___2180_74999.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___2180_74999.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___2180_74999.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___2180_74999.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___2180_74999.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___2180_74999.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___2180_74999.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___2180_74999.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___2180_74999.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___2180_74999.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___2180_74999.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___2180_74999.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___2180_74999.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___2180_74999.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___2180_74999.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___2180_74999.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___2180_74999.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___2180_74999.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___2180_74999.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___2180_74999.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___2180_74999.FStar_TypeChecker_Env.nbe)
                                }  in
                              let uu____75004 =
                                mk_irrelevant_goal "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                  g1.FStar_Tactics_Types.label
                                 in
                              bind uu____75004
                                (fun goal  ->
                                   mlog
                                     (fun uu____75014  ->
                                        let uu____75015 =
                                          goal_to_string_verbose g1  in
                                        let uu____75017 =
                                          goal_to_string_verbose g2  in
                                        let uu____75019 =
                                          goal_to_string_verbose goal  in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____75015 uu____75017 uu____75019)
                                     (fun uu____75023  -> ret goal))))))
  
let (join : unit -> unit tac) =
  fun uu____75031  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____75047 =
               set
                 (let uu___2195_75052 = ps  in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___2195_75052.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.main_goal =
                      (uu___2195_75052.FStar_Tactics_Types.main_goal);
                    FStar_Tactics_Types.all_implicits =
                      (uu___2195_75052.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___2195_75052.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___2195_75052.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___2195_75052.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___2195_75052.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___2195_75052.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___2195_75052.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___2195_75052.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___2195_75052.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___2195_75052.FStar_Tactics_Types.local_state)
                  })
                in
             bind uu____75047
               (fun uu____75055  ->
                  let uu____75056 = join_goals g1 g2  in
                  bind uu____75056 (fun g12  -> add_goals [g12]))
         | uu____75061 -> fail "join: less than 2 goals")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) tac)
  =
  fun t  ->
    let uu____75083 =
      let uu____75090 = cur_goal ()  in
      bind uu____75090
        (fun g  ->
           let uu____75100 =
             let uu____75109 = FStar_Tactics_Types.goal_env g  in
             __tc uu____75109 t  in
           bind uu____75100
             (fun uu____75137  ->
                match uu____75137 with
                | (t1,typ,guard) ->
                    let uu____75153 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____75153 with
                     | (hd1,args) ->
                         let uu____75202 =
                           let uu____75217 =
                             let uu____75218 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____75218.FStar_Syntax_Syntax.n  in
                           (uu____75217, args)  in
                         (match uu____75202 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____75239)::(q,uu____75241)::[]) when
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
                                let uu____75295 =
                                  let uu____75296 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____75296
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____75295
                                 in
                              let g2 =
                                let uu____75298 =
                                  let uu____75299 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____75299
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____75298
                                 in
                              bind __dismiss
                                (fun uu____75306  ->
                                   let uu____75307 = add_goals [g1; g2]  in
                                   bind uu____75307
                                     (fun uu____75316  ->
                                        let uu____75317 =
                                          let uu____75322 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____75323 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____75322, uu____75323)  in
                                        ret uu____75317))
                          | uu____75328 ->
                              let uu____75343 =
                                let uu____75345 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____75345 typ  in
                              fail1 "Not a disjunction: %s" uu____75343))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____75083
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____75380 =
      let uu____75383 = cur_goal ()  in
      bind uu____75383
        (fun g  ->
           FStar_Options.push ();
           (let uu____75396 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____75396);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___2232_75403 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___2232_75403.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___2232_75403.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___2232_75403.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___2232_75403.FStar_Tactics_Types.label)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____75380
  
let (top_env : unit -> env tac) =
  fun uu____75420  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____75435  ->
    let uu____75439 = cur_goal ()  in
    bind uu____75439
      (fun g  ->
         let uu____75446 =
           (FStar_Options.lax ()) ||
             (let uu____75449 = FStar_Tactics_Types.goal_env g  in
              uu____75449.FStar_TypeChecker_Env.lax)
            in
         ret uu____75446)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____75466 =
        mlog
          (fun uu____75471  ->
             let uu____75472 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____75472)
          (fun uu____75477  ->
             let uu____75478 = cur_goal ()  in
             bind uu____75478
               (fun goal  ->
                  let env =
                    let uu____75486 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____75486 ty  in
                  let uu____75487 = __tc_ghost env tm  in
                  bind uu____75487
                    (fun uu____75506  ->
                       match uu____75506 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____75520  ->
                                let uu____75521 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____75521)
                             (fun uu____75525  ->
                                mlog
                                  (fun uu____75528  ->
                                     let uu____75529 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____75529)
                                  (fun uu____75534  ->
                                     let uu____75535 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____75535
                                       (fun uu____75540  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____75466
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____75565 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____75571 =
              let uu____75578 =
                let uu____75579 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____75579
                 in
              new_uvar "uvar_env.2" env uu____75578  in
            bind uu____75571
              (fun uu____75596  ->
                 match uu____75596 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____75565
        (fun typ  ->
           let uu____75608 = new_uvar "uvar_env" env typ  in
           bind uu____75608
             (fun uu____75623  ->
                match uu____75623 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____75642 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____75661 -> g.FStar_Tactics_Types.opts
             | uu____75664 -> FStar_Options.peek ()  in
           let uu____75667 = FStar_Syntax_Util.head_and_args t  in
           match uu____75667 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____75687);
                FStar_Syntax_Syntax.pos = uu____75688;
                FStar_Syntax_Syntax.vars = uu____75689;_},uu____75690)
               ->
               let env1 =
                 let uu___2286_75732 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___2286_75732.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___2286_75732.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___2286_75732.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___2286_75732.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___2286_75732.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___2286_75732.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___2286_75732.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___2286_75732.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___2286_75732.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___2286_75732.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___2286_75732.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___2286_75732.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___2286_75732.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___2286_75732.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___2286_75732.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___2286_75732.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___2286_75732.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___2286_75732.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___2286_75732.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___2286_75732.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___2286_75732.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___2286_75732.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___2286_75732.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___2286_75732.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___2286_75732.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___2286_75732.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___2286_75732.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___2286_75732.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___2286_75732.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___2286_75732.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___2286_75732.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___2286_75732.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___2286_75732.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___2286_75732.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___2286_75732.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___2286_75732.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___2286_75732.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___2286_75732.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___2286_75732.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___2286_75732.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___2286_75732.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___2286_75732.FStar_TypeChecker_Env.nbe)
                 }  in
               let g =
                 FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false ""  in
               let uu____75736 =
                 let uu____75739 = bnorm_goal g  in [uu____75739]  in
               add_goals uu____75736
           | uu____75740 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____75642
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____75802 = if b then t2 else ret false  in
             bind uu____75802 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____75828 = trytac comp  in
      bind uu____75828
        (fun uu___613_75840  ->
           match uu___613_75840 with
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
        let uu____75882 =
          bind get
            (fun ps  ->
               let uu____75890 = __tc e t1  in
               bind uu____75890
                 (fun uu____75911  ->
                    match uu____75911 with
                    | (t11,ty1,g1) ->
                        let uu____75924 = __tc e t2  in
                        bind uu____75924
                          (fun uu____75945  ->
                             match uu____75945 with
                             | (t21,ty2,g2) ->
                                 let uu____75958 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____75958
                                   (fun uu____75965  ->
                                      let uu____75966 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____75966
                                        (fun uu____75974  ->
                                           let uu____75975 =
                                             do_unify e ty1 ty2  in
                                           let uu____75979 =
                                             do_unify e t11 t21  in
                                           tac_and uu____75975 uu____75979)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____75882
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____76027  ->
             let uu____76028 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____76028
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
        (fun uu____76062  ->
           let uu____76063 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____76063)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____76074 =
      mlog
        (fun uu____76079  ->
           let uu____76080 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____76080)
        (fun uu____76085  ->
           let uu____76086 = cur_goal ()  in
           bind uu____76086
             (fun g  ->
                let uu____76092 =
                  let uu____76101 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____76101 ty  in
                bind uu____76092
                  (fun uu____76113  ->
                     match uu____76113 with
                     | (ty1,uu____76123,guard) ->
                         let uu____76125 =
                           let uu____76128 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____76128 guard  in
                         bind uu____76125
                           (fun uu____76132  ->
                              let uu____76133 =
                                let uu____76137 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____76138 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____76137 uu____76138 ty1  in
                              bind uu____76133
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____76147 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____76147
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops]  in
                                      let ng =
                                        let uu____76154 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____76155 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____76154
                                          uu____76155
                                         in
                                      let nty =
                                        let uu____76157 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____76157 ty1  in
                                      let uu____76158 =
                                        let uu____76162 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____76162 ng nty  in
                                      bind uu____76158
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____76171 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____76171
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____76074
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) Prims.list tac)
  =
  fun s_tm  ->
    let uu____76245 =
      let uu____76254 = cur_goal ()  in
      bind uu____76254
        (fun g  ->
           let uu____76266 =
             let uu____76275 = FStar_Tactics_Types.goal_env g  in
             __tc uu____76275 s_tm  in
           bind uu____76266
             (fun uu____76293  ->
                match uu____76293 with
                | (s_tm1,s_ty,guard) ->
                    let uu____76311 =
                      let uu____76314 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____76314 guard  in
                    bind uu____76311
                      (fun uu____76327  ->
                         let uu____76328 =
                           FStar_Syntax_Util.head_and_args' s_ty  in
                         match uu____76328 with
                         | (h,args) ->
                             let uu____76373 =
                               let uu____76380 =
                                 let uu____76381 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____76381.FStar_Syntax_Syntax.n  in
                               match uu____76380 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____76396;
                                      FStar_Syntax_Syntax.vars = uu____76397;_},us)
                                   -> ret (fv, us)
                               | uu____76407 -> fail "type is not an fv"  in
                             bind uu____76373
                               (fun uu____76428  ->
                                  match uu____76428 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____76444 =
                                        let uu____76447 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____76447 t_lid
                                         in
                                      (match uu____76444 with
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
                                                  (fun uu____76498  ->
                                                     let uu____76499 =
                                                       FStar_Syntax_Subst.open_term
                                                         t_ps t_ty
                                                        in
                                                     match uu____76499 with
                                                     | (t_ps1,t_ty1) ->
                                                         let uu____76514 =
                                                           mapM
                                                             (fun c_lid  ->
                                                                let uu____76542
                                                                  =
                                                                  let uu____76545
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                  FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____76545
                                                                    c_lid
                                                                   in
                                                                match uu____76542
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
                                                                    uu____76619
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
                                                                    let uu____76624
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____76624
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____76647
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____76647
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____76690
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs
                                                                     in
                                                                    (match uu____76690
                                                                    with
                                                                    | 
                                                                    (d_ps,bs1)
                                                                    ->
                                                                    let uu____76763
                                                                    =
                                                                    let uu____76765
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp  in
                                                                    Prims.op_Negation
                                                                    uu____76765
                                                                     in
                                                                    failwhen
                                                                    uu____76763
                                                                    "not total?"
                                                                    (fun
                                                                    uu____76784
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
                                                                    uu___614_76801
                                                                    =
                                                                    match uu___614_76801
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____76805)
                                                                    -> true
                                                                    | 
                                                                    uu____76808
                                                                    -> false
                                                                     in
                                                                    let uu____76812
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____76812
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
                                                                    uu____76946
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
                                                                    uu____77008
                                                                     ->
                                                                    match uu____77008
                                                                    with
                                                                    | 
                                                                    ((bv,uu____77028),
                                                                    (t,uu____77030))
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
                                                                    uu____77100
                                                                     ->
                                                                    match uu____77100
                                                                    with
                                                                    | 
                                                                    ((bv,uu____77127),
                                                                    (t,uu____77129))
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
                                                                    uu____77188
                                                                     ->
                                                                    match uu____77188
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
                                                                    let uu____77243
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___2450_77260
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___2450_77260.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___2450_77260.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___2450_77260.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___2450_77260.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___2450_77260.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___2450_77260.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___2450_77260.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___2450_77260.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___2450_77260.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___2450_77260.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___2450_77260.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___2450_77260.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___2450_77260.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___2450_77260.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___2450_77260.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___2450_77260.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___2450_77260.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___2450_77260.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___2450_77260.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___2450_77260.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___2450_77260.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___2450_77260.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___2450_77260.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___2450_77260.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___2450_77260.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___2450_77260.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___2450_77260.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___2450_77260.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___2450_77260.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___2450_77260.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___2450_77260.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___2450_77260.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___2450_77260.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___2450_77260.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___2450_77260.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___2450_77260.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___2450_77260.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___2450_77260.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___2450_77260.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___2450_77260.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___2450_77260.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___2450_77260.FStar_TypeChecker_Env.nbe)
                                                                    }) s_ty
                                                                    pat  in
                                                                    match uu____77243
                                                                    with
                                                                    | 
                                                                    (uu____77274,uu____77275,uu____77276,pat_t,uu____77278,_guard_pat)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____77285
                                                                    =
                                                                    let uu____77286
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____77286
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____77285
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____77291
                                                                    =
                                                                    let uu____77300
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____77300]
                                                                     in
                                                                    let uu____77319
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____77291
                                                                    uu____77319
                                                                     in
                                                                    let nty =
                                                                    let uu____77325
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____77325
                                                                     in
                                                                    let uu____77328
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____77328
                                                                    (fun
                                                                    uu____77358
                                                                     ->
                                                                    match uu____77358
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
                                                                    let uu____77385
                                                                    =
                                                                    let uu____77396
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____77396]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____77385
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____77432
                                                                    =
                                                                    let uu____77443
                                                                    =
                                                                    let uu____77448
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2)  in
                                                                    (fv1,
                                                                    uu____77448)
                                                                     in
                                                                    (g', br,
                                                                    uu____77443)
                                                                     in
                                                                    ret
                                                                    uu____77432))))))
                                                                    | 
                                                                    uu____77469
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                             c_lids
                                                            in
                                                         bind uu____76514
                                                           (fun goal_brs  ->
                                                              let uu____77519
                                                                =
                                                                FStar_List.unzip3
                                                                  goal_brs
                                                                 in
                                                              match uu____77519
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
                                                                  let uu____77592
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                  bind
                                                                    uu____77592
                                                                    (
                                                                    fun
                                                                    uu____77603
                                                                     ->
                                                                    let uu____77604
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____77604
                                                                    (fun
                                                                    uu____77614
                                                                     ->
                                                                    ret infos))))
                                            | uu____77621 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____76245
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____77670::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____77700 = init xs  in x :: uu____77700
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____77713 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      let t3 = FStar_Syntax_Util.unlazy_emb t2  in
      match t3.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____77722) -> inspect t4
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____77788 = last args  in
          (match uu____77788 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____77818 =
                 let uu____77819 =
                   let uu____77824 =
                     let uu____77825 =
                       let uu____77830 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____77830  in
                     uu____77825 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____77824, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____77819  in
               FStar_All.pipe_left ret uu____77818)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____77841,uu____77842) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
          let uu____77895 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____77895 with
           | (bs1,t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____77937 =
                      let uu____77938 =
                        let uu____77943 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____77943)  in
                      FStar_Reflection_Data.Tv_Abs uu____77938  in
                    FStar_All.pipe_left ret uu____77937))
      | FStar_Syntax_Syntax.Tm_type uu____77946 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____77971 ->
          let uu____77986 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____77986 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____78017 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____78017 with
           | (b',t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____78070 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____78083 =
            let uu____78084 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____78084  in
          FStar_All.pipe_left ret uu____78083
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____78105 =
            let uu____78106 =
              let uu____78111 =
                let uu____78112 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____78112  in
              (uu____78111, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____78106  in
          FStar_All.pipe_left ret uu____78105
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____78152 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____78157 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____78157 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____78210 ->
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
             | FStar_Util.Inr uu____78252 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____78256 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____78256 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____78276 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____78282 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____78337 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____78337
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____78358 =
                  let uu____78365 =
                    FStar_List.map
                      (fun uu____78378  ->
                         match uu____78378 with
                         | (p1,uu____78387) -> inspect_pat p1) ps
                     in
                  (fv, uu____78365)  in
                FStar_Reflection_Data.Pat_Cons uu____78358
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
              (fun uu___615_78483  ->
                 match uu___615_78483 with
                 | (pat,uu____78505,t5) ->
                     let uu____78523 = inspect_pat pat  in (uu____78523, t5))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____78532 ->
          ((let uu____78534 =
              let uu____78540 =
                let uu____78542 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____78544 = FStar_Syntax_Print.term_to_string t3  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____78542 uu____78544
                 in
              (FStar_Errors.Warning_CantInspect, uu____78540)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____78534);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____77713
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____78562 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____78562
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____78566 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____78566
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____78570 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____78570
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____78577 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____78577
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____78602 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____78602
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____78619 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____78619
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____78638 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____78638
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____78642 =
          let uu____78643 =
            let uu____78650 =
              let uu____78651 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____78651  in
            FStar_Syntax_Syntax.mk uu____78650  in
          uu____78643 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____78642
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____78656 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____78656
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____78667 =
          let uu____78668 =
            let uu____78675 =
              let uu____78676 =
                let uu____78690 =
                  let uu____78693 =
                    let uu____78694 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____78694]  in
                  FStar_Syntax_Subst.close uu____78693 t2  in
                ((false, [lb]), uu____78690)  in
              FStar_Syntax_Syntax.Tm_let uu____78676  in
            FStar_Syntax_Syntax.mk uu____78675  in
          uu____78668 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____78667
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____78736 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____78736 with
         | (lbs,body) ->
             let uu____78751 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____78751)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____78788 =
                let uu____78789 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____78789  in
              FStar_All.pipe_left wrap uu____78788
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____78796 =
                let uu____78797 =
                  let uu____78811 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____78829 = pack_pat p1  in
                         (uu____78829, false)) ps
                     in
                  (fv, uu____78811)  in
                FStar_Syntax_Syntax.Pat_cons uu____78797  in
              FStar_All.pipe_left wrap uu____78796
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
            (fun uu___616_78878  ->
               match uu___616_78878 with
               | (pat,t1) ->
                   let uu____78895 = pack_pat pat  in
                   (uu____78895, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____78943 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____78943
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____78971 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____78971
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____79017 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____79017
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____79056 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____79056
  
let (lget :
  FStar_Reflection_Data.typ -> Prims.string -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun k  ->
      let uu____79076 =
        bind get
          (fun ps  ->
             let uu____79082 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____79082 with
             | FStar_Pervasives_Native.None  -> fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
      FStar_All.pipe_left (wrap_err "lget") uu____79076
  
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit tac)
  =
  fun _ty  ->
    fun k  ->
      fun t  ->
        let uu____79116 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___2748_79123 = ps  in
                 let uu____79124 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t
                    in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___2748_79123.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___2748_79123.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___2748_79123.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___2748_79123.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___2748_79123.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___2748_79123.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___2748_79123.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___2748_79123.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___2748_79123.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___2748_79123.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___2748_79123.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___2748_79123.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____79124
                 }  in
               set ps1)
           in
        FStar_All.pipe_left (wrap_err "lset") uu____79116
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal * FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun typ  ->
      let uu____79151 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____79151 with
      | (u,ctx_uvars,g_u) ->
          let uu____79184 = FStar_List.hd ctx_uvars  in
          (match uu____79184 with
           | (ctx_uvar,uu____79198) ->
               let g =
                 let uu____79200 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____79200 false
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
        let uu____79223 = goal_of_goal_ty env typ  in
        match uu____79223 with
        | (g,g_u) ->
            let ps =
              let uu____79235 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "TacVerbose")
                 in
              let uu____79238 = FStar_Util.psmap_empty ()  in
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
                FStar_Tactics_Types.tac_verb_dbg = uu____79235;
                FStar_Tactics_Types.local_state = uu____79238
              }  in
            let uu____79248 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____79248)
  