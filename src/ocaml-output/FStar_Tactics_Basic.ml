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
    let uu____63907 =
      let uu____63908 = FStar_Tactics_Types.goal_env g  in
      let uu____63909 = FStar_Tactics_Types.goal_type g  in
      bnorm uu____63908 uu____63909  in
    FStar_Tactics_Types.goal_with_type g uu____63907
  
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
      let uu____64023 = FStar_Options.tactics_failhard ()  in
      if uu____64023
      then run t p
      else
        (try (fun uu___640_64033  -> match () with | () -> run t p) ()
         with
         | FStar_Errors.Err (uu____64042,msg) ->
             FStar_Tactics_Result.Failed
               ((FStar_Tactics_Types.TacticFailure msg), p)
         | FStar_Errors.Error (uu____64046,msg,uu____64048) ->
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
           let uu____64128 = run t1 p  in
           match uu____64128 with
           | FStar_Tactics_Result.Success (a,q) ->
               let uu____64135 = t2 a  in run uu____64135 q
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
    let uu____64158 =
      FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head  in
    match uu____64158 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (check_goal_solved :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun goal  -> get_uvar_solved goal.FStar_Tactics_Types.goal_ctx_uvar 
let (goal_to_string_verbose : FStar_Tactics_Types.goal -> Prims.string) =
  fun g  ->
    let uu____64180 =
      FStar_Syntax_Print.ctx_uvar_to_string
        g.FStar_Tactics_Types.goal_ctx_uvar
       in
    let uu____64182 =
      let uu____64184 = check_goal_solved g  in
      match uu____64184 with
      | FStar_Pervasives_Native.None  -> ""
      | FStar_Pervasives_Native.Some t ->
          let uu____64190 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "\tGOAL ALREADY SOLVED!: %s" uu____64190
       in
    FStar_Util.format2 "%s%s\n" uu____64180 uu____64182
  
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
            let uu____64237 = FStar_Options.print_implicits ()  in
            if uu____64237
            then
              let uu____64241 = FStar_Tactics_Types.goal_env g  in
              let uu____64242 = FStar_Tactics_Types.goal_witness g  in
              tts uu____64241 uu____64242
            else
              (let uu____64245 =
                 get_uvar_solved g.FStar_Tactics_Types.goal_ctx_uvar  in
               match uu____64245 with
               | FStar_Pervasives_Native.None  -> "_"
               | FStar_Pervasives_Native.Some t ->
                   let uu____64251 = FStar_Tactics_Types.goal_env g  in
                   let uu____64252 = FStar_Tactics_Types.goal_witness g  in
                   tts uu____64251 uu____64252)
             in
          let num =
            match maybe_num with
            | FStar_Pervasives_Native.None  -> ""
            | FStar_Pervasives_Native.Some (i,n1) ->
                let uu____64275 = FStar_Util.string_of_int i  in
                let uu____64277 = FStar_Util.string_of_int n1  in
                FStar_Util.format2 " %s/%s" uu____64275 uu____64277
             in
          let maybe_label =
            match g.FStar_Tactics_Types.label with
            | "" -> ""
            | l -> Prims.op_Hat " (" (Prims.op_Hat l ")")  in
          let actual_goal =
            if ps.FStar_Tactics_Types.tac_verb_dbg
            then goal_to_string_verbose g
            else
              (let uu____64295 =
                 FStar_Syntax_Print.binders_to_string ", "
                   (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
                  in
               let uu____64298 =
                 let uu____64300 = FStar_Tactics_Types.goal_env g  in
                 tts uu____64300
                   (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                  in
               FStar_Util.format3 "%s |- %s : %s\n" uu____64295 w uu____64298)
             in
          FStar_Util.format4 "%s%s%s:\n%s\n" kind num maybe_label actual_goal
  
let (tacprint : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      let uu____64327 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____64327
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____64352 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____64352
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____64384 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____64384
  
let (comp_to_typ : FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____64394) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____64404) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (get_phi :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun g  ->
    let uu____64424 =
      let uu____64425 = FStar_Tactics_Types.goal_env g  in
      let uu____64426 = FStar_Tactics_Types.goal_type g  in
      FStar_TypeChecker_Normalize.unfold_whnf uu____64425 uu____64426  in
    FStar_Syntax_Util.un_squash uu____64424
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  -> let uu____64435 = get_phi g  in FStar_Option.isSome uu____64435 
let (print : Prims.string -> unit tac) = fun msg  -> tacprint msg; ret () 
let (debugging : unit -> Prims.bool tac) =
  fun uu____64459  ->
    bind get
      (fun ps  ->
         let uu____64467 =
           FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
             (FStar_Options.Other "Tac")
            in
         ret uu____64467)
  
let (ps_to_string :
  (Prims.string * FStar_Tactics_Types.proofstate) -> Prims.string) =
  fun uu____64482  ->
    match uu____64482 with
    | (msg,ps) ->
        let p_imp imp =
          FStar_Syntax_Print.uvar_to_string
            (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
           in
        let n_active = FStar_List.length ps.FStar_Tactics_Types.goals  in
        let n_smt = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
        let n1 = n_active + n_smt  in
        let uu____64504 =
          let uu____64508 =
            let uu____64512 =
              let uu____64514 =
                FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
              FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____64514
                msg
               in
            let uu____64517 =
              let uu____64521 =
                if
                  ps.FStar_Tactics_Types.entry_range <>
                    FStar_Range.dummyRange
                then
                  let uu____64525 =
                    FStar_Range.string_of_def_range
                      ps.FStar_Tactics_Types.entry_range
                     in
                  FStar_Util.format1 "Location: %s\n" uu____64525
                else ""  in
              let uu____64531 =
                let uu____64535 =
                  let uu____64537 =
                    FStar_TypeChecker_Env.debug
                      ps.FStar_Tactics_Types.main_context
                      (FStar_Options.Other "Imp")
                     in
                  if uu____64537
                  then
                    let uu____64542 =
                      FStar_Common.string_of_list p_imp
                        ps.FStar_Tactics_Types.all_implicits
                       in
                    FStar_Util.format1 "Imps: %s\n" uu____64542
                  else ""  in
                [uu____64535]  in
              uu____64521 :: uu____64531  in
            uu____64512 :: uu____64517  in
          let uu____64552 =
            let uu____64556 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "Goal"
                       (FStar_Pervasives_Native.Some
                          (((Prims.parse_int "1") + i), n1)) ps g)
                ps.FStar_Tactics_Types.goals
               in
            let uu____64576 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "SMT Goal"
                       (FStar_Pervasives_Native.Some
                          ((((Prims.parse_int "1") + n_active) + i), n1)) ps
                       g) ps.FStar_Tactics_Types.smt_goals
               in
            FStar_List.append uu____64556 uu____64576  in
          FStar_List.append uu____64508 uu____64552  in
        FStar_String.concat "" uu____64504
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      let uu____64606 =
        let uu____64607 = FStar_Tactics_Types.goal_env g  in
        FStar_TypeChecker_Env.all_binders uu____64607  in
      let uu____64608 =
        let uu____64613 =
          let uu____64614 = FStar_Tactics_Types.goal_env g  in
          FStar_TypeChecker_Env.dsenv uu____64614  in
        FStar_Syntax_Print.binders_to_json uu____64613  in
      FStar_All.pipe_right uu____64606 uu____64608  in
    let uu____64615 =
      let uu____64623 =
        let uu____64631 =
          let uu____64637 =
            let uu____64638 =
              let uu____64646 =
                let uu____64652 =
                  let uu____64653 =
                    let uu____64655 = FStar_Tactics_Types.goal_env g  in
                    let uu____64656 = FStar_Tactics_Types.goal_witness g  in
                    tts uu____64655 uu____64656  in
                  FStar_Util.JsonStr uu____64653  in
                ("witness", uu____64652)  in
              let uu____64659 =
                let uu____64667 =
                  let uu____64673 =
                    let uu____64674 =
                      let uu____64676 = FStar_Tactics_Types.goal_env g  in
                      let uu____64677 = FStar_Tactics_Types.goal_type g  in
                      tts uu____64676 uu____64677  in
                    FStar_Util.JsonStr uu____64674  in
                  ("type", uu____64673)  in
                [uu____64667;
                ("label", (FStar_Util.JsonStr (g.FStar_Tactics_Types.label)))]
                 in
              uu____64646 :: uu____64659  in
            FStar_Util.JsonAssoc uu____64638  in
          ("goal", uu____64637)  in
        [uu____64631]  in
      ("hyps", g_binders) :: uu____64623  in
    FStar_Util.JsonAssoc uu____64615
  
let (ps_to_json :
  (Prims.string * FStar_Tactics_Types.proofstate) -> FStar_Util.json) =
  fun uu____64731  ->
    match uu____64731 with
    | (msg,ps) ->
        let uu____64741 =
          let uu____64749 =
            let uu____64757 =
              let uu____64765 =
                let uu____64773 =
                  let uu____64779 =
                    let uu____64780 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____64780  in
                  ("goals", uu____64779)  in
                let uu____64785 =
                  let uu____64793 =
                    let uu____64799 =
                      let uu____64800 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____64800  in
                    ("smt-goals", uu____64799)  in
                  [uu____64793]  in
                uu____64773 :: uu____64785  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____64765
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____64757  in
          let uu____64834 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____64850 =
                let uu____64856 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____64856)  in
              [uu____64850]
            else []  in
          FStar_List.append uu____64749 uu____64834  in
        FStar_Util.JsonAssoc uu____64741
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____64896  ->
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
         (let uu____64927 = FStar_Tactics_Types.subst_proof_state subst1 ps
             in
          dump_proofstate uu____64927 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let traise : 'a . Prims.exn -> 'a tac =
  fun e  -> mk_tac (fun ps  -> FStar_Tactics_Result.Failed (e, ps)) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____65000 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____65000
          then dump_proofstate ps (Prims.op_Hat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed
           ((FStar_Tactics_Types.TacticFailure msg), ps))
  
let fail1 : 'Auu____65014 . Prims.string -> Prims.string -> 'Auu____65014 tac
  =
  fun msg  ->
    fun x  -> let uu____65031 = FStar_Util.format1 msg x  in fail uu____65031
  
let fail2 :
  'Auu____65042 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____65042 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        let uu____65066 = FStar_Util.format2 msg x y  in fail uu____65066
  
let fail3 :
  'Auu____65079 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____65079 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____65110 = FStar_Util.format3 msg x y z  in fail uu____65110
  
let fail4 :
  'Auu____65125 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____65125 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____65163 = FStar_Util.format4 msg x y z w  in
            fail uu____65163
  
let catch : 'a . 'a tac -> (Prims.exn,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____65198 = run t ps  in
         match uu____65198 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___802_65222 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___802_65222.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___802_65222.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___802_65222.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___802_65222.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___802_65222.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___802_65222.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___802_65222.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___802_65222.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___802_65222.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___802_65222.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___802_65222.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (uu___802_65222.FStar_Tactics_Types.local_state)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let recover : 'a . 'a tac -> (Prims.exn,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let uu____65261 = run t ps  in
         match uu____65261 with
         | FStar_Tactics_Result.Success (a,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inr a), q)
         | FStar_Tactics_Result.Failed (m,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inl m), q))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____65309 = catch t  in
    bind uu____65309
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____65336 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try
           (fun uu___828_65368  ->
              match () with
              | () -> let uu____65373 = trytac t  in run uu____65373 ps) ()
         with
         | FStar_Errors.Err (uu____65389,msg) ->
             (log ps
                (fun uu____65395  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____65401,msg,uu____65403) ->
             (log ps
                (fun uu____65408  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____65445 = run t ps  in
           match uu____65445 with
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
  fun p  -> mk_tac (fun uu____65469  -> FStar_Tactics_Result.Success ((), p)) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___863_65484 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___863_65484.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___863_65484.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___863_65484.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___863_65484.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___863_65484.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___863_65484.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___863_65484.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___863_65484.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___863_65484.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___863_65484.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___863_65484.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___863_65484.FStar_Tactics_Types.local_state)
            }))
  
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____65508 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____65508
         then
           let uu____65512 = FStar_Syntax_Print.term_to_string t1  in
           let uu____65514 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____65512
             uu____65514
         else ());
        (try
           (fun uu___871_65525  ->
              match () with
              | () ->
                  let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
                  ((let uu____65533 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____65533
                    then
                      let uu____65537 =
                        FStar_Common.string_of_option
                          (FStar_TypeChecker_Rel.guard_to_string env) res
                         in
                      let uu____65539 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____65541 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.print3
                        "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____65537
                        uu____65539 uu____65541
                    else ());
                   (match res with
                    | FStar_Pervasives_Native.None  -> ret false
                    | FStar_Pervasives_Native.Some g ->
                        let uu____65552 =
                          add_implicits g.FStar_TypeChecker_Env.implicits  in
                        bind uu____65552 (fun uu____65557  -> ret true)))) ()
         with
         | FStar_Errors.Err (uu____65567,msg) ->
             mlog
               (fun uu____65573  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____65576  -> ret false)
         | FStar_Errors.Error (uu____65579,msg,r) ->
             mlog
               (fun uu____65587  ->
                  let uu____65588 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____65588) (fun uu____65592  -> ret false))
  
let (compress_implicits : unit tac) =
  bind get
    (fun ps  ->
       let imps = ps.FStar_Tactics_Types.all_implicits  in
       let g =
         let uu___897_65606 = FStar_TypeChecker_Env.trivial_guard  in
         {
           FStar_TypeChecker_Env.guard_f =
             (uu___897_65606.FStar_TypeChecker_Env.guard_f);
           FStar_TypeChecker_Env.deferred =
             (uu___897_65606.FStar_TypeChecker_Env.deferred);
           FStar_TypeChecker_Env.univ_ineqs =
             (uu___897_65606.FStar_TypeChecker_Env.univ_ineqs);
           FStar_TypeChecker_Env.implicits = imps
         }  in
       let g1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g
          in
       let ps' =
         let uu___901_65609 = ps  in
         {
           FStar_Tactics_Types.main_context =
             (uu___901_65609.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___901_65609.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (g1.FStar_TypeChecker_Env.implicits);
           FStar_Tactics_Types.goals =
             (uu___901_65609.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___901_65609.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___901_65609.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___901_65609.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___901_65609.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___901_65609.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___901_65609.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___901_65609.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___901_65609.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___901_65609.FStar_Tactics_Types.local_state)
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
          (fun uu____65636  ->
             (let uu____65638 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____65638
              then
                (FStar_Options.push ();
                 (let uu____65643 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____65647 = __do_unify env t1 t2  in
              bind uu____65647
                (fun r  ->
                   (let uu____65658 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____65658 then FStar_Options.pop () else ());
                   ret r)))
  
let (remove_solved_goals : unit tac) =
  bind get
    (fun ps  ->
       let ps' =
         let uu___916_65672 = ps  in
         let uu____65673 =
           FStar_List.filter
             (fun g  ->
                let uu____65679 = check_goal_solved g  in
                FStar_Option.isNone uu____65679) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___916_65672.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___916_65672.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___916_65672.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____65673;
           FStar_Tactics_Types.smt_goals =
             (uu___916_65672.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___916_65672.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___916_65672.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___916_65672.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___916_65672.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___916_65672.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___916_65672.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___916_65672.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___916_65672.FStar_Tactics_Types.local_state)
         }  in
       set ps')
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____65697 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____65697 with
      | FStar_Pervasives_Native.Some uu____65702 ->
          let uu____65703 =
            let uu____65705 = goal_to_string_verbose goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____65705  in
          fail uu____65703
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____65726 = FStar_Tactics_Types.goal_env goal  in
      let uu____65727 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____65726 solution uu____65727
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____65734 =
         let uu___929_65735 = p  in
         let uu____65736 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___929_65735.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___929_65735.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___929_65735.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____65736;
           FStar_Tactics_Types.smt_goals =
             (uu___929_65735.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___929_65735.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___929_65735.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___929_65735.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___929_65735.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___929_65735.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___929_65735.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___929_65735.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___929_65735.FStar_Tactics_Types.local_state)
         }  in
       set uu____65734)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      mlog
        (fun uu____65758  ->
           let uu____65759 =
             let uu____65761 = FStar_Tactics_Types.goal_witness goal  in
             FStar_Syntax_Print.term_to_string uu____65761  in
           let uu____65762 = FStar_Syntax_Print.term_to_string solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____65759 uu____65762)
        (fun uu____65767  ->
           let uu____65768 = trysolve goal solution  in
           bind uu____65768
             (fun b  ->
                if b
                then bind __dismiss (fun uu____65780  -> remove_solved_goals)
                else
                  (let uu____65783 =
                     let uu____65785 =
                       let uu____65787 = FStar_Tactics_Types.goal_env goal
                          in
                       tts uu____65787 solution  in
                     let uu____65788 =
                       let uu____65790 = FStar_Tactics_Types.goal_env goal
                          in
                       let uu____65791 =
                         FStar_Tactics_Types.goal_witness goal  in
                       tts uu____65790 uu____65791  in
                     let uu____65792 =
                       let uu____65794 = FStar_Tactics_Types.goal_env goal
                          in
                       let uu____65795 = FStar_Tactics_Types.goal_type goal
                          in
                       tts uu____65794 uu____65795  in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____65785 uu____65788 uu____65792
                      in
                   fail uu____65783)))
  
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____65812 = set_solution goal solution  in
      bind uu____65812
        (fun uu____65816  ->
           bind __dismiss (fun uu____65818  -> remove_solved_goals))
  
let (set_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___945_65837 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___945_65837.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___945_65837.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___945_65837.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals = gs;
              FStar_Tactics_Types.smt_goals =
                (uu___945_65837.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___945_65837.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___945_65837.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___945_65837.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___945_65837.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___945_65837.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___945_65837.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___945_65837.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___945_65837.FStar_Tactics_Types.local_state)
            }))
  
let (set_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___949_65856 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___949_65856.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___949_65856.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___949_65856.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___949_65856.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals = gs;
              FStar_Tactics_Types.depth =
                (uu___949_65856.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___949_65856.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___949_65856.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___949_65856.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___949_65856.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___949_65856.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___949_65856.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___949_65856.FStar_Tactics_Types.local_state)
            }))
  
let (dismiss_all : unit tac) = set_goals [] 
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____65872 = FStar_Options.defensive ()  in
    if uu____65872
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____65882 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____65882)
         in
      let b2 =
        b1 &&
          (let uu____65886 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____65886)
         in
      let rec aux b3 e =
        let uu____65901 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____65901 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____65921 =
        (let uu____65925 = aux b2 env  in Prims.op_Negation uu____65925) &&
          (let uu____65928 = FStar_ST.op_Bang nwarn  in
           uu____65928 < (Prims.parse_int "5"))
         in
      (if uu____65921
       then
         ((let uu____65954 =
             let uu____65955 = FStar_Tactics_Types.goal_type g  in
             uu____65955.FStar_Syntax_Syntax.pos  in
           let uu____65958 =
             let uu____65964 =
               let uu____65966 = goal_to_string_verbose g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____65966
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____65964)  in
           FStar_Errors.log_issue uu____65954 uu____65958);
          (let uu____65970 =
             let uu____65972 = FStar_ST.op_Bang nwarn  in
             uu____65972 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____65970))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___971_66041 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___971_66041.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___971_66041.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___971_66041.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___971_66041.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___971_66041.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___971_66041.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___971_66041.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___971_66041.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___971_66041.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___971_66041.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___971_66041.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___971_66041.FStar_Tactics_Types.local_state)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___976_66062 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___976_66062.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___976_66062.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___976_66062.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___976_66062.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___976_66062.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___976_66062.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___976_66062.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___976_66062.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___976_66062.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___976_66062.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___976_66062.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___976_66062.FStar_Tactics_Types.local_state)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___981_66083 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___981_66083.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___981_66083.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___981_66083.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___981_66083.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___981_66083.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___981_66083.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___981_66083.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___981_66083.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___981_66083.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___981_66083.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___981_66083.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___981_66083.FStar_Tactics_Types.local_state)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___986_66104 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___986_66104.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___986_66104.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___986_66104.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___986_66104.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___986_66104.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___986_66104.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___986_66104.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___986_66104.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___986_66104.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___986_66104.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___986_66104.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___986_66104.FStar_Tactics_Types.local_state)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____66116  -> add_goals [g]) 
let (new_uvar :
  Prims.string ->
    env ->
      FStar_Reflection_Data.typ ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar) tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____66147 =
          FStar_TypeChecker_Env.new_implicit_var_aux reason
            typ.FStar_Syntax_Syntax.pos env typ
            FStar_Syntax_Syntax.Allow_untyped FStar_Pervasives_Native.None
           in
        match uu____66147 with
        | (u,ctx_uvar,g_u) ->
            let uu____66185 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____66185
              (fun uu____66194  ->
                 let uu____66195 =
                   let uu____66200 =
                     let uu____66201 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____66201  in
                   (u, uu____66200)  in
                 ret uu____66195)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____66222 = FStar_Syntax_Util.un_squash t1  in
    match uu____66222 with
    | FStar_Pervasives_Native.Some t' ->
        let t'1 = FStar_Syntax_Util.unascribe t'  in
        let uu____66234 =
          let uu____66235 = FStar_Syntax_Subst.compress t'1  in
          uu____66235.FStar_Syntax_Syntax.n  in
        (match uu____66234 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____66240 -> false)
    | uu____66242 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____66255 = FStar_Syntax_Util.un_squash t  in
    match uu____66255 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____66266 =
          let uu____66267 = FStar_Syntax_Subst.compress t'  in
          uu____66267.FStar_Syntax_Syntax.n  in
        (match uu____66266 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____66272 -> false)
    | uu____66274 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____66287  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____66299 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____66299 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____66306 = goal_to_string_verbose hd1  in
                    let uu____66308 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____66306 uu____66308);
                   ret hd1)))
  
let (tadmit_t : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____66321 =
      bind get
        (fun ps  ->
           let uu____66327 = cur_goal ()  in
           bind uu____66327
             (fun g  ->
                (let uu____66334 =
                   let uu____66335 = FStar_Tactics_Types.goal_type g  in
                   uu____66335.FStar_Syntax_Syntax.pos  in
                 let uu____66338 =
                   let uu____66344 =
                     let uu____66346 =
                       goal_to_string "" FStar_Pervasives_Native.None ps g
                        in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____66346
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____66344)  in
                 FStar_Errors.log_issue uu____66334 uu____66338);
                solve' g t))
       in
    FStar_All.pipe_left (wrap_err "tadmit_t") uu____66321
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____66369  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___1031_66380 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___1031_66380.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___1031_66380.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___1031_66380.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___1031_66380.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___1031_66380.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___1031_66380.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___1031_66380.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___1031_66380.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___1031_66380.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___1031_66380.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___1031_66380.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (uu___1031_66380.FStar_Tactics_Types.local_state)
           }  in
         let uu____66382 = set ps1  in
         bind uu____66382
           (fun uu____66387  ->
              let uu____66388 = FStar_BigInt.of_int_fs n1  in ret uu____66388))
  
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
              let uu____66426 = env.FStar_TypeChecker_Env.universe_of env phi
                 in
              FStar_Syntax_Util.mk_squash uu____66426 phi  in
            let uu____66427 = new_uvar reason env typ  in
            bind uu____66427
              (fun uu____66442  ->
                 match uu____66442 with
                 | (uu____66449,ctx_uvar) ->
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
             (fun uu____66496  ->
                let uu____66497 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____66497)
             (fun uu____66502  ->
                let e1 =
                  let uu___1049_66504 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1049_66504.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1049_66504.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1049_66504.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1049_66504.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1049_66504.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1049_66504.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1049_66504.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1049_66504.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1049_66504.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1049_66504.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1049_66504.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1049_66504.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1049_66504.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1049_66504.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1049_66504.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1049_66504.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1049_66504.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1049_66504.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1049_66504.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1049_66504.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1049_66504.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1049_66504.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1049_66504.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1049_66504.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1049_66504.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1049_66504.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1049_66504.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1049_66504.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1049_66504.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1049_66504.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1049_66504.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1049_66504.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1049_66504.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1049_66504.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1049_66504.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1049_66504.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1049_66504.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1049_66504.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1049_66504.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1049_66504.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1049_66504.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1049_66504.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___1053_66516  ->
                     match () with
                     | () ->
                         let uu____66525 =
                           FStar_TypeChecker_TcTerm.type_of_tot_term e1 t  in
                         ret uu____66525) ()
                with
                | FStar_Errors.Err (uu____66552,msg) ->
                    let uu____66556 = tts e1 t  in
                    let uu____66558 =
                      let uu____66560 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____66560
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____66556 uu____66558 msg
                | FStar_Errors.Error (uu____66570,msg,uu____66572) ->
                    let uu____66575 = tts e1 t  in
                    let uu____66577 =
                      let uu____66579 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____66579
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____66575 uu____66577 msg))
  
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
             (fun uu____66632  ->
                let uu____66633 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc_ghost(%s)\n" uu____66633)
             (fun uu____66638  ->
                let e1 =
                  let uu___1070_66640 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1070_66640.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1070_66640.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1070_66640.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1070_66640.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1070_66640.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1070_66640.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1070_66640.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1070_66640.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1070_66640.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1070_66640.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1070_66640.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1070_66640.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1070_66640.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1070_66640.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1070_66640.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1070_66640.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1070_66640.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1070_66640.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1070_66640.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1070_66640.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1070_66640.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1070_66640.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1070_66640.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1070_66640.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1070_66640.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1070_66640.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1070_66640.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1070_66640.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1070_66640.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1070_66640.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1070_66640.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1070_66640.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1070_66640.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1070_66640.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1070_66640.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1070_66640.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1070_66640.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1070_66640.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1070_66640.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1070_66640.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1070_66640.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1070_66640.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___1074_66655  ->
                     match () with
                     | () ->
                         let uu____66664 =
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e1 t
                            in
                         (match uu____66664 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____66702,msg) ->
                    let uu____66706 = tts e1 t  in
                    let uu____66708 =
                      let uu____66710 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____66710
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____66706 uu____66708 msg
                | FStar_Errors.Error (uu____66720,msg,uu____66722) ->
                    let uu____66725 = tts e1 t  in
                    let uu____66727 =
                      let uu____66729 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____66729
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____66725 uu____66727 msg))
  
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
             (fun uu____66782  ->
                let uu____66783 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____66783)
             (fun uu____66789  ->
                let e1 =
                  let uu___1095_66791 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1095_66791.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1095_66791.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1095_66791.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1095_66791.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1095_66791.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1095_66791.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1095_66791.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1095_66791.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1095_66791.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1095_66791.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1095_66791.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1095_66791.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1095_66791.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1095_66791.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1095_66791.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1095_66791.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1095_66791.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1095_66791.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1095_66791.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1095_66791.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1095_66791.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1095_66791.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1095_66791.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1095_66791.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1095_66791.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1095_66791.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1095_66791.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1095_66791.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1095_66791.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1095_66791.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1095_66791.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1095_66791.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1095_66791.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1095_66791.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1095_66791.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1095_66791.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1095_66791.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1095_66791.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1095_66791.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1095_66791.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1095_66791.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1095_66791.FStar_TypeChecker_Env.nbe)
                  }  in
                let e2 =
                  let uu___1098_66794 = e1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1098_66794.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1098_66794.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1098_66794.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1098_66794.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1098_66794.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1098_66794.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1098_66794.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1098_66794.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1098_66794.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1098_66794.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1098_66794.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1098_66794.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1098_66794.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1098_66794.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1098_66794.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1098_66794.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1098_66794.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1098_66794.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1098_66794.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1098_66794.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1098_66794.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1098_66794.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1098_66794.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1098_66794.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___1098_66794.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1098_66794.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1098_66794.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1098_66794.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1098_66794.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1098_66794.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1098_66794.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1098_66794.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1098_66794.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1098_66794.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1098_66794.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1098_66794.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1098_66794.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1098_66794.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1098_66794.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1098_66794.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1098_66794.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1098_66794.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___1102_66809  ->
                     match () with
                     | () ->
                         let uu____66818 =
                           FStar_TypeChecker_TcTerm.tc_term e2 t  in
                         (match uu____66818 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____66856,msg) ->
                    let uu____66860 = tts e2 t  in
                    let uu____66862 =
                      let uu____66864 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____66864
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____66860 uu____66862 msg
                | FStar_Errors.Error (uu____66874,msg,uu____66876) ->
                    let uu____66879 = tts e2 t  in
                    let uu____66881 =
                      let uu____66883 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____66883
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____66879 uu____66881 msg))
  
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
  fun uu____66917  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___1127_66936 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___1127_66936.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___1127_66936.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___1127_66936.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___1127_66936.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___1127_66936.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___1127_66936.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___1127_66936.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___1127_66936.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___1127_66936.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___1127_66936.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___1127_66936.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___1127_66936.FStar_Tactics_Types.local_state)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____66961 = get_guard_policy ()  in
      bind uu____66961
        (fun old_pol  ->
           let uu____66967 = set_guard_policy pol  in
           bind uu____66967
             (fun uu____66971  ->
                bind t
                  (fun r  ->
                     let uu____66975 = set_guard_policy old_pol  in
                     bind uu____66975 (fun uu____66979  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____66983 = let uu____66988 = cur_goal ()  in trytac uu____66988  in
  bind uu____66983
    (fun uu___609_66995  ->
       match uu___609_66995 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____67001 = FStar_Options.peek ()  in ret uu____67001)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        mlog
          (fun uu____67026  ->
             let uu____67027 = FStar_TypeChecker_Rel.guard_to_string e g  in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason
               uu____67027)
          (fun uu____67032  ->
             let uu____67033 =
               add_implicits g.FStar_TypeChecker_Env.implicits  in
             bind uu____67033
               (fun uu____67037  ->
                  bind getopts
                    (fun opts  ->
                       let uu____67041 =
                         let uu____67042 =
                           FStar_TypeChecker_Rel.simplify_guard e g  in
                         uu____67042.FStar_TypeChecker_Env.guard_f  in
                       match uu____67041 with
                       | FStar_TypeChecker_Common.Trivial  -> ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____67046 = istrivial e f  in
                           if uu____67046
                           then ret ()
                           else
                             bind get
                               (fun ps  ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop  ->
                                      ((let uu____67059 =
                                          let uu____67065 =
                                            let uu____67067 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g
                                               in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____67067
                                             in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____67065)
                                           in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____67059);
                                       ret ())
                                  | FStar_Tactics_Types.Goal  ->
                                      mlog
                                        (fun uu____67073  ->
                                           let uu____67074 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____67074)
                                        (fun uu____67079  ->
                                           let uu____67080 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____67080
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___1156_67088 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___1156_67088.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___1156_67088.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___1156_67088.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___1156_67088.FStar_Tactics_Types.label)
                                                  }  in
                                                push_goals [goal1]))
                                  | FStar_Tactics_Types.SMT  ->
                                      mlog
                                        (fun uu____67092  ->
                                           let uu____67093 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____67093)
                                        (fun uu____67098  ->
                                           let uu____67099 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____67099
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___1163_67107 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___1163_67107.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___1163_67107.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___1163_67107.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___1163_67107.FStar_Tactics_Types.label)
                                                  }  in
                                                push_smt_goals [goal1]))
                                  | FStar_Tactics_Types.Force  ->
                                      mlog
                                        (fun uu____67111  ->
                                           let uu____67112 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____67112)
                                        (fun uu____67116  ->
                                           try
                                             (fun uu___1170_67121  ->
                                                match () with
                                                | () ->
                                                    let uu____67124 =
                                                      let uu____67126 =
                                                        let uu____67128 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____67128
                                                         in
                                                      Prims.op_Negation
                                                        uu____67126
                                                       in
                                                    if uu____67124
                                                    then
                                                      mlog
                                                        (fun uu____67135  ->
                                                           let uu____67136 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g
                                                              in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____67136)
                                                        (fun uu____67140  ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else ret ()) ()
                                           with
                                           | uu___1169_67145 ->
                                               mlog
                                                 (fun uu____67150  ->
                                                    let uu____67151 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g
                                                       in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____67151)
                                                 (fun uu____67155  ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____67167 =
      let uu____67170 = cur_goal ()  in
      bind uu____67170
        (fun goal  ->
           let uu____67176 =
             let uu____67185 = FStar_Tactics_Types.goal_env goal  in
             __tc_lax uu____67185 t  in
           bind uu____67176
             (fun uu____67196  ->
                match uu____67196 with
                | (uu____67205,typ,uu____67207) -> ret typ))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____67167
  
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
            let uu____67247 = mk_irrelevant_goal reason env phi opts label1
               in
            bind uu____67247 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____67259  ->
    let uu____67262 = cur_goal ()  in
    bind uu____67262
      (fun goal  ->
         let uu____67268 =
           let uu____67270 = FStar_Tactics_Types.goal_env goal  in
           let uu____67271 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____67270 uu____67271  in
         if uu____67268
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____67277 =
              let uu____67279 = FStar_Tactics_Types.goal_env goal  in
              let uu____67280 = FStar_Tactics_Types.goal_type goal  in
              tts uu____67279 uu____67280  in
            fail1 "Not a trivial goal: %s" uu____67277))
  
let divide : 'a 'b . FStar_BigInt.t -> 'a tac -> 'b tac -> ('a * 'b) tac =
  fun n1  ->
    fun l  ->
      fun r  ->
        bind get
          (fun p  ->
             let uu____67331 =
               try
                 (fun uu___1226_67354  ->
                    match () with
                    | () ->
                        let uu____67365 =
                          let uu____67374 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____67374
                            p.FStar_Tactics_Types.goals
                           in
                        ret uu____67365) ()
               with | uu___1225_67385 -> fail "divide: not enough goals"  in
             bind uu____67331
               (fun uu____67422  ->
                  match uu____67422 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___1208_67448 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___1208_67448.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___1208_67448.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___1208_67448.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___1208_67448.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___1208_67448.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___1208_67448.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___1208_67448.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___1208_67448.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___1208_67448.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___1208_67448.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___1208_67448.FStar_Tactics_Types.local_state)
                        }  in
                      let uu____67449 = set lp  in
                      bind uu____67449
                        (fun uu____67457  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___1214_67473 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___1214_67473.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___1214_67473.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___1214_67473.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___1214_67473.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___1214_67473.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___1214_67473.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___1214_67473.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___1214_67473.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___1214_67473.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___1214_67473.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___1214_67473.FStar_Tactics_Types.local_state)
                                       }  in
                                     let uu____67474 = set rp  in
                                     bind uu____67474
                                       (fun uu____67482  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___1220_67498 =
                                                        rp'  in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___1220_67498.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___1220_67498.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___1220_67498.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___1220_67498.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___1220_67498.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___1220_67498.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___1220_67498.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___1220_67498.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___1220_67498.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___1220_67498.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___1220_67498.FStar_Tactics_Types.local_state)
                                                      }  in
                                                    let uu____67499 = set p'
                                                       in
                                                    bind uu____67499
                                                      (fun uu____67507  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____67513 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____67535 = divide FStar_BigInt.one f idtac  in
    bind uu____67535
      (fun uu____67548  -> match uu____67548 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____67586::uu____67587 ->
             let uu____67590 =
               let uu____67599 = map tau  in
               divide FStar_BigInt.one tau uu____67599  in
             bind uu____67590
               (fun uu____67617  ->
                  match uu____67617 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____67659 =
        bind t1
          (fun uu____67664  ->
             let uu____67665 = map t2  in
             bind uu____67665 (fun uu____67673  -> ret ()))
         in
      focus uu____67659
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____67683  ->
    let uu____67686 =
      let uu____67689 = cur_goal ()  in
      bind uu____67689
        (fun goal  ->
           let uu____67698 =
             let uu____67705 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____67705  in
           match uu____67698 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____67714 =
                 let uu____67716 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____67716  in
               if uu____67714
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____67725 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____67725 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____67739 = new_uvar "intro" env' typ'  in
                  bind uu____67739
                    (fun uu____67756  ->
                       match uu____67756 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c))
                              in
                           let uu____67780 = set_solution goal sol  in
                           bind uu____67780
                             (fun uu____67786  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                    goal.FStar_Tactics_Types.label
                                   in
                                let uu____67788 =
                                  let uu____67791 = bnorm_goal g  in
                                  replace_cur uu____67791  in
                                bind uu____67788 (fun uu____67793  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____67798 =
                 let uu____67800 = FStar_Tactics_Types.goal_env goal  in
                 let uu____67801 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____67800 uu____67801  in
               fail1 "goal is not an arrow (%s)" uu____67798)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____67686
  
let (intro_rec :
  unit -> (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder) tac) =
  fun uu____67819  ->
    let uu____67826 = cur_goal ()  in
    bind uu____67826
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____67845 =
            let uu____67852 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____67852  in
          match uu____67845 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____67865 =
                let uu____67867 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____67867  in
              if uu____67865
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____67884 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____67884
                    in
                 let bs =
                   let uu____67895 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____67895; b]  in
                 let env' =
                   let uu____67921 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____67921 bs  in
                 let uu____67922 =
                   let uu____67929 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____67929  in
                 bind uu____67922
                   (fun uu____67949  ->
                      match uu____67949 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____67963 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____67966 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____67963
                              FStar_Parser_Const.effect_Tot_lid uu____67966
                              [] FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____67984 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____67984 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____68006 =
                                   let uu____68007 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____68007.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____68006
                                  in
                               let uu____68023 = set_solution goal tm  in
                               bind uu____68023
                                 (fun uu____68032  ->
                                    let uu____68033 =
                                      let uu____68036 =
                                        bnorm_goal
                                          (let uu___1291_68039 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___1291_68039.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___1291_68039.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___1291_68039.FStar_Tactics_Types.is_guard);
                                             FStar_Tactics_Types.label =
                                               (uu___1291_68039.FStar_Tactics_Types.label)
                                           })
                                         in
                                      replace_cur uu____68036  in
                                    bind uu____68033
                                      (fun uu____68046  ->
                                         let uu____68047 =
                                           let uu____68052 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____68052, b)  in
                                         ret uu____68047)))))
          | FStar_Pervasives_Native.None  ->
              let uu____68061 =
                let uu____68063 = FStar_Tactics_Types.goal_env goal  in
                let uu____68064 = FStar_Tactics_Types.goal_type goal  in
                tts uu____68063 uu____68064  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____68061))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____68084 = cur_goal ()  in
    bind uu____68084
      (fun goal  ->
         mlog
           (fun uu____68091  ->
              let uu____68092 =
                let uu____68094 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____68094  in
              FStar_Util.print1 "norm: witness = %s\n" uu____68092)
           (fun uu____68100  ->
              let steps =
                let uu____68104 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____68104
                 in
              let t =
                let uu____68108 = FStar_Tactics_Types.goal_env goal  in
                let uu____68109 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____68108 uu____68109  in
              let uu____68110 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____68110))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____68135 =
          bind get
            (fun ps  ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
                 | g::uu____68143 -> g.FStar_Tactics_Types.opts
                 | uu____68146 -> FStar_Options.peek ()  in
               mlog
                 (fun uu____68151  ->
                    let uu____68152 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____68152)
                 (fun uu____68157  ->
                    let uu____68158 = __tc_lax e t  in
                    bind uu____68158
                      (fun uu____68179  ->
                         match uu____68179 with
                         | (t1,uu____68189,uu____68190) ->
                             let steps =
                               let uu____68194 =
                                 FStar_TypeChecker_Normalize.tr_norm_steps s
                                  in
                               FStar_List.append
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu____68194
                                in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1
                                in
                             mlog
                               (fun uu____68200  ->
                                  let uu____68201 =
                                    FStar_Syntax_Print.term_to_string t2  in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____68201)
                               (fun uu____68205  -> ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____68135
  
let (refine_intro : unit -> unit tac) =
  fun uu____68218  ->
    let uu____68221 =
      let uu____68224 = cur_goal ()  in
      bind uu____68224
        (fun g  ->
           let uu____68231 =
             let uu____68242 = FStar_Tactics_Types.goal_env g  in
             let uu____68243 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____68242
               uu____68243
              in
           match uu____68231 with
           | (uu____68246,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____68272 =
                 let uu____68277 =
                   let uu____68282 =
                     let uu____68283 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____68283]  in
                   FStar_Syntax_Subst.open_term uu____68282 phi  in
                 match uu____68277 with
                 | (bvs,phi1) ->
                     let uu____68308 =
                       let uu____68309 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____68309  in
                     (uu____68308, phi1)
                  in
               (match uu____68272 with
                | (bv1,phi1) ->
                    let uu____68328 =
                      let uu____68331 = FStar_Tactics_Types.goal_env g  in
                      let uu____68332 =
                        let uu____68333 =
                          let uu____68336 =
                            let uu____68337 =
                              let uu____68344 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____68344)  in
                            FStar_Syntax_Syntax.NT uu____68337  in
                          [uu____68336]  in
                        FStar_Syntax_Subst.subst uu____68333 phi1  in
                      mk_irrelevant_goal "refine_intro refinement"
                        uu____68331 uu____68332 g.FStar_Tactics_Types.opts
                        g.FStar_Tactics_Types.label
                       in
                    bind uu____68328
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____68353  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____68221
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____68376 = cur_goal ()  in
      bind uu____68376
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____68385 = FStar_Tactics_Types.goal_env goal  in
               let uu____68386 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____68385 uu____68386
             else FStar_Tactics_Types.goal_env goal  in
           let uu____68389 = __tc env t  in
           bind uu____68389
             (fun uu____68408  ->
                match uu____68408 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____68423  ->
                         let uu____68424 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____68426 =
                           let uu____68428 =
                             FStar_Tactics_Types.goal_env goal  in
                           FStar_TypeChecker_Rel.guard_to_string uu____68428
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____68424 uu____68426)
                      (fun uu____68432  ->
                         let uu____68433 =
                           let uu____68436 =
                             FStar_Tactics_Types.goal_env goal  in
                           proc_guard "__exact typing" uu____68436 guard  in
                         bind uu____68433
                           (fun uu____68439  ->
                              mlog
                                (fun uu____68443  ->
                                   let uu____68444 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____68446 =
                                     let uu____68448 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____68448
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____68444 uu____68446)
                                (fun uu____68452  ->
                                   let uu____68453 =
                                     let uu____68457 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____68458 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____68457 typ uu____68458  in
                                   bind uu____68453
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____68468 =
                                             let uu____68470 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____68470 t1  in
                                           let uu____68471 =
                                             let uu____68473 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____68473 typ  in
                                           let uu____68474 =
                                             let uu____68476 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____68477 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____68476 uu____68477  in
                                           let uu____68478 =
                                             let uu____68480 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____68481 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____68480 uu____68481  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____68468 uu____68471
                                             uu____68474 uu____68478)))))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun try_refine  ->
    fun set_expected_typ1  ->
      fun tm  ->
        let uu____68507 =
          mlog
            (fun uu____68512  ->
               let uu____68513 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____68513)
            (fun uu____68518  ->
               let uu____68519 =
                 let uu____68526 = __exact_now set_expected_typ1 tm  in
                 catch uu____68526  in
               bind uu____68519
                 (fun uu___611_68535  ->
                    match uu___611_68535 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        traise e
                    | FStar_Util.Inl e ->
                        mlog
                          (fun uu____68546  ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____68550  ->
                             let uu____68551 =
                               let uu____68558 =
                                 let uu____68561 =
                                   norm [FStar_Syntax_Embeddings.Delta]  in
                                 bind uu____68561
                                   (fun uu____68566  ->
                                      let uu____68567 = refine_intro ()  in
                                      bind uu____68567
                                        (fun uu____68571  ->
                                           __exact_now set_expected_typ1 tm))
                                  in
                               catch uu____68558  in
                             bind uu____68551
                               (fun uu___610_68578  ->
                                  match uu___610_68578 with
                                  | FStar_Util.Inr r ->
                                      mlog
                                        (fun uu____68587  ->
                                           FStar_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu____68590  -> ret ())
                                  | FStar_Util.Inl uu____68591 ->
                                      mlog
                                        (fun uu____68593  ->
                                           FStar_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu____68596  -> traise e)))))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____68507
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____68648 = f x  in
          bind uu____68648
            (fun y  ->
               let uu____68656 = mapM f xs  in
               bind uu____68656 (fun ys  -> ret (y :: ys)))
  
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
          let uu____68728 = do_unify e ty1 ty2  in
          bind uu____68728
            (fun uu___612_68742  ->
               if uu___612_68742
               then ret acc
               else
                 (let uu____68762 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____68762 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____68783 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____68785 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____68783
                        uu____68785
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____68802 =
                        let uu____68804 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____68804  in
                      if uu____68802
                      then fail "Codomain is effectful"
                      else
                        (let uu____68828 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____68828
                           (fun uu____68855  ->
                              match uu____68855 with
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
      let uu____68945 =
        mlog
          (fun uu____68950  ->
             let uu____68951 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_apply: tm = %s\n" uu____68951)
          (fun uu____68956  ->
             let uu____68957 = cur_goal ()  in
             bind uu____68957
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____68965 = __tc e tm  in
                  bind uu____68965
                    (fun uu____68986  ->
                       match uu____68986 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____68999 =
                             let uu____69010 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____69010  in
                           bind uu____68999
                             (fun uvs  ->
                                let fix_qual q =
                                  match q with
                                  | FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Meta uu____69048)
                                      ->
                                      FStar_Pervasives_Native.Some
                                        (FStar_Syntax_Syntax.Implicit false)
                                  | uu____69052 -> q  in
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____69075  ->
                                       fun w  ->
                                         match uu____69075 with
                                         | (uvt,q,uu____69093) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, (fix_qual q))]) uvs tm1
                                   in
                                let uvset =
                                  let uu____69125 =
                                    FStar_Syntax_Free.new_uv_set ()  in
                                  FStar_List.fold_right
                                    (fun uu____69142  ->
                                       fun s  ->
                                         match uu____69142 with
                                         | (uu____69154,uu____69155,uv) ->
                                             let uu____69157 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                in
                                             FStar_Util.set_union s
                                               uu____69157) uvs uu____69125
                                   in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset  in
                                let uu____69167 = solve' goal w  in
                                bind uu____69167
                                  (fun uu____69172  ->
                                     let uu____69173 =
                                       mapM
                                         (fun uu____69190  ->
                                            match uu____69190 with
                                            | (uvt,q,uv) ->
                                                let uu____69202 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                   in
                                                (match uu____69202 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____69207 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____69208 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv)
                                                        in
                                                     if uu____69208
                                                     then ret ()
                                                     else
                                                       (let uu____69215 =
                                                          let uu____69218 =
                                                            bnorm_goal
                                                              (let uu___1452_69221
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___1452_69221.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___1452_69221.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false;
                                                                 FStar_Tactics_Types.label
                                                                   =
                                                                   (uu___1452_69221.FStar_Tactics_Types.label)
                                                               })
                                                             in
                                                          [uu____69218]  in
                                                        add_goals uu____69215)))
                                         uvs
                                        in
                                     bind uu____69173
                                       (fun uu____69226  ->
                                          proc_guard "apply guard" e guard))))))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____68945
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____69254 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____69254
    then
      let uu____69263 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____69278 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____69331 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____69263 with
      | (pre,post) ->
          let post1 =
            let uu____69364 =
              let uu____69375 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____69375]  in
            FStar_Syntax_Util.mk_app post uu____69364  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____69406 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____69406
       then
         let uu____69415 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____69415
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
            let uu____69494 = f x e  in
            bind uu____69494 (fun e'  -> fold_left f e' xs1)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____69509 =
      let uu____69512 =
        bind get
          (fun ps  ->
             mlog
               (fun uu____69519  ->
                  let uu____69520 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____69520)
               (fun uu____69526  ->
                  let is_unit_t t =
                    let uu____69534 =
                      let uu____69535 = FStar_Syntax_Subst.compress t  in
                      uu____69535.FStar_Syntax_Syntax.n  in
                    match uu____69534 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____69541 -> false  in
                  let uu____69543 = cur_goal ()  in
                  bind uu____69543
                    (fun goal  ->
                       let uu____69549 =
                         let uu____69558 = FStar_Tactics_Types.goal_env goal
                            in
                         __tc uu____69558 tm  in
                       bind uu____69549
                         (fun uu____69573  ->
                            match uu____69573 with
                            | (tm1,t,guard) ->
                                let uu____69585 =
                                  FStar_Syntax_Util.arrow_formals_comp t  in
                                (match uu____69585 with
                                 | (bs,comp) ->
                                     let uu____69618 = lemma_or_sq comp  in
                                     (match uu____69618 with
                                      | FStar_Pervasives_Native.None  ->
                                          fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre,post) ->
                                          let uu____69638 =
                                            fold_left
                                              (fun uu____69700  ->
                                                 fun uu____69701  ->
                                                   match (uu____69700,
                                                           uu____69701)
                                                   with
                                                   | ((b,aq),(uvs,imps,subst1))
                                                       ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst1
                                                           b.FStar_Syntax_Syntax.sort
                                                          in
                                                       let uu____69852 =
                                                         is_unit_t b_t  in
                                                       if uu____69852
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
                                                         (let uu____69975 =
                                                            let uu____69982 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            new_uvar
                                                              "apply_lemma"
                                                              uu____69982 b_t
                                                             in
                                                          bind uu____69975
                                                            (fun uu____70013 
                                                               ->
                                                               match uu____70013
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
                                          bind uu____69638
                                            (fun uu____70199  ->
                                               match uu____70199 with
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
                                                   let uu____70287 =
                                                     let uu____70291 =
                                                       FStar_Tactics_Types.goal_env
                                                         goal
                                                        in
                                                     let uu____70292 =
                                                       FStar_Syntax_Util.mk_squash
                                                         FStar_Syntax_Syntax.U_zero
                                                         post1
                                                        in
                                                     let uu____70293 =
                                                       FStar_Tactics_Types.goal_type
                                                         goal
                                                        in
                                                     do_unify uu____70291
                                                       uu____70292
                                                       uu____70293
                                                      in
                                                   bind uu____70287
                                                     (fun b  ->
                                                        if
                                                          Prims.op_Negation b
                                                        then
                                                          let uu____70304 =
                                                            let uu____70306 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            tts uu____70306
                                                              tm1
                                                             in
                                                          let uu____70307 =
                                                            let uu____70309 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            let uu____70310 =
                                                              FStar_Syntax_Util.mk_squash
                                                                FStar_Syntax_Syntax.U_zero
                                                                post1
                                                               in
                                                            tts uu____70309
                                                              uu____70310
                                                             in
                                                          let uu____70311 =
                                                            let uu____70313 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            let uu____70314 =
                                                              FStar_Tactics_Types.goal_type
                                                                goal
                                                               in
                                                            tts uu____70313
                                                              uu____70314
                                                             in
                                                          fail3
                                                            "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                            uu____70304
                                                            uu____70307
                                                            uu____70311
                                                        else
                                                          (let uu____70318 =
                                                             solve' goal
                                                               FStar_Syntax_Util.exp_unit
                                                              in
                                                           bind uu____70318
                                                             (fun uu____70326
                                                                 ->
                                                                let is_free_uvar
                                                                  uv t1 =
                                                                  let free_uvars
                                                                    =
                                                                    let uu____70352
                                                                    =
                                                                    let uu____70355
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____70355
                                                                     in
                                                                    FStar_List.map
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____70352
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
                                                                    let uu____70391
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____70391)
                                                                    goals
                                                                   in
                                                                let checkone
                                                                  t1 goals =
                                                                  let uu____70408
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                  match uu____70408
                                                                  with
                                                                  | (hd1,uu____70427)
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____70454)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____70471
                                                                    -> false)
                                                                   in
                                                                let uu____70473
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
                                                                    let uu____70516
                                                                    = imp  in
                                                                    match uu____70516
                                                                    with
                                                                    | 
                                                                    (term,ctx_uvar)
                                                                    ->
                                                                    let uu____70527
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____70527
                                                                    with
                                                                    | 
                                                                    (hd1,uu____70549)
                                                                    ->
                                                                    let uu____70574
                                                                    =
                                                                    let uu____70575
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____70575.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____70574
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____70583)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___1562_70603
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___1562_70603.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___1562_70603.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___1562_70603.FStar_Tactics_Types.is_guard);
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___1562_70603.FStar_Tactics_Types.label)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____70606
                                                                    ->
                                                                    mlog
                                                                    (fun
                                                                    uu____70612
                                                                     ->
                                                                    let uu____70613
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                                                     in
                                                                    let uu____70615
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____70613
                                                                    uu____70615)
                                                                    (fun
                                                                    uu____70622
                                                                     ->
                                                                    let env =
                                                                    let uu___1567_70624
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___1567_70624.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1567_70624.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1567_70624.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___1567_70624.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1567_70624.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1567_70624.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1567_70624.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1567_70624.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___1567_70624.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___1567_70624.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___1567_70624.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1567_70624.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1567_70624.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1567_70624.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1567_70624.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1567_70624.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1567_70624.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1567_70624.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___1567_70624.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___1567_70624.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___1567_70624.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1567_70624.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1567_70624.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1567_70624.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1567_70624.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1567_70624.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1567_70624.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1567_70624.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1567_70624.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1567_70624.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1567_70624.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1567_70624.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1567_70624.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1567_70624.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___1567_70624.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1567_70624.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1567_70624.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___1567_70624.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1567_70624.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1567_70624.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1567_70624.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1567_70624.FStar_TypeChecker_Env.nbe)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let uu____70627
                                                                    =
                                                                    let uu____70630
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____70634
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
                                                                    let uu____70636
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____70634
                                                                    uu____70636
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____70642
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    uu____70630
                                                                    uu____70642
                                                                    g_typ  in
                                                                    bind
                                                                    uu____70627
                                                                    (fun
                                                                    uu____70646
                                                                     ->
                                                                    ret []))))))
                                                                   in
                                                                bind
                                                                  uu____70473
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
                                                                    let uu____70710
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____70710
                                                                    then
                                                                    let uu____70715
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____70715
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
                                                                    let uu____70730
                                                                    =
                                                                    let uu____70732
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____70732
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____70730)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____70733
                                                                    =
                                                                    let uu____70736
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____70736
                                                                    guard  in
                                                                    bind
                                                                    uu____70733
                                                                    (fun
                                                                    uu____70740
                                                                     ->
                                                                    let uu____70741
                                                                    =
                                                                    let uu____70744
                                                                    =
                                                                    let uu____70746
                                                                    =
                                                                    let uu____70748
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____70749
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____70748
                                                                    uu____70749
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____70746
                                                                     in
                                                                    if
                                                                    uu____70744
                                                                    then
                                                                    let uu____70753
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____70753
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    goal.FStar_Tactics_Types.label
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____70741
                                                                    (fun
                                                                    uu____70758
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2)))))))))))))
         in
      focus uu____69512  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____69509
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____70782 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____70782 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____70792::(e1,uu____70794)::(e2,uu____70796)::[])) when
        (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) ||
          (FStar_Ident.lid_equals l FStar_Parser_Const.c_eq2_lid)
        -> FStar_Pervasives_Native.Some (e1, e2)
    | uu____70857 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____70882 = destruct_eq' typ  in
    match uu____70882 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____70912 = FStar_Syntax_Util.un_squash typ  in
        (match uu____70912 with
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
        let uu____70981 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____70981 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', bv', [])
            else
              (let uu____71039 = aux e'  in
               FStar_Util.map_opt uu____71039
                 (fun uu____71070  ->
                    match uu____71070 with
                    | (e'',bv,bvs) -> (e'', bv, (bv' :: bvs))))
         in
      let uu____71096 = aux e  in
      FStar_Util.map_opt uu____71096
        (fun uu____71127  ->
           match uu____71127 with
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
          let uu____71201 =
            let uu____71212 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____71212  in
          FStar_Util.map_opt uu____71201
            (fun uu____71230  ->
               match uu____71230 with
               | (e0,b11,bvs) ->
                   let s1 bv =
                     let uu___1640_71252 = bv  in
                     let uu____71253 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___1640_71252.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___1640_71252.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____71253
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___1644_71261 =
                       g.FStar_Tactics_Types.goal_ctx_uvar  in
                     let uu____71262 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____71271 =
                       let uu____71274 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____71274  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___1644_71261.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____71262;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____71271;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___1644_71261.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___1644_71261.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___1644_71261.FStar_Syntax_Syntax.ctx_uvar_range);
                       FStar_Syntax_Syntax.ctx_uvar_meta =
                         (uu___1644_71261.FStar_Syntax_Syntax.ctx_uvar_meta)
                     }  in
                   let uu___1647_71275 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1647_71275.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___1647_71275.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___1647_71275.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1647_71275.FStar_Tactics_Types.label)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____71286 =
      let uu____71289 = cur_goal ()  in
      bind uu____71289
        (fun goal  ->
           let uu____71297 = h  in
           match uu____71297 with
           | (bv,uu____71301) ->
               mlog
                 (fun uu____71309  ->
                    let uu____71310 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____71312 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____71310
                      uu____71312)
                 (fun uu____71317  ->
                    let uu____71318 =
                      let uu____71329 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____71329  in
                    match uu____71318 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                        let uu____71356 =
                          destruct_eq bv1.FStar_Syntax_Syntax.sort  in
                        (match uu____71356 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____71371 =
                               let uu____71372 =
                                 FStar_Syntax_Subst.compress x  in
                               uu____71372.FStar_Syntax_Syntax.n  in
                             (match uu____71371 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv2 =
                                    let uu___1670_71389 = bv2  in
                                    let uu____71390 =
                                      FStar_Syntax_Subst.subst s
                                        bv2.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1670_71389.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1670_71389.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____71390
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv1 :: bvs1)  in
                                  let new_goal =
                                    let uu___1674_71398 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____71399 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____71408 =
                                      let uu____71411 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____71411
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___1674_71398.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____71399;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____71408;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___1674_71398.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___1674_71398.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___1674_71398.FStar_Syntax_Syntax.ctx_uvar_range);
                                      FStar_Syntax_Syntax.ctx_uvar_meta =
                                        (uu___1674_71398.FStar_Syntax_Syntax.ctx_uvar_meta)
                                    }  in
                                  replace_cur
                                    (let uu___1677_71414 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___1677_71414.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___1677_71414.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___1677_71414.FStar_Tactics_Types.is_guard);
                                       FStar_Tactics_Types.label =
                                         (uu___1677_71414.FStar_Tactics_Types.label)
                                     })
                              | uu____71415 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____71417 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____71286
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____71447 =
        let uu____71450 = cur_goal ()  in
        bind uu____71450
          (fun goal  ->
             let uu____71461 = b  in
             match uu____71461 with
             | (bv,uu____71465) ->
                 let bv' =
                   let uu____71471 =
                     let uu___1688_71472 = bv  in
                     let uu____71473 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____71473;
                       FStar_Syntax_Syntax.index =
                         (uu___1688_71472.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___1688_71472.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____71471  in
                 let s1 =
                   let uu____71478 =
                     let uu____71479 =
                       let uu____71486 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____71486)  in
                     FStar_Syntax_Syntax.NT uu____71479  in
                   [uu____71478]  in
                 let uu____71491 = subst_goal bv bv' s1 goal  in
                 (match uu____71491 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____71447
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____71513 =
      let uu____71516 = cur_goal ()  in
      bind uu____71516
        (fun goal  ->
           let uu____71525 = b  in
           match uu____71525 with
           | (bv,uu____71529) ->
               let uu____71534 =
                 let uu____71545 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____71545  in
               (match uu____71534 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                    let uu____71572 = FStar_Syntax_Util.type_u ()  in
                    (match uu____71572 with
                     | (ty,u) ->
                         let uu____71581 = new_uvar "binder_retype" e0 ty  in
                         bind uu____71581
                           (fun uu____71600  ->
                              match uu____71600 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___1712_71610 = bv1  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1712_71610.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1712_71610.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____71614 =
                                      let uu____71615 =
                                        let uu____71622 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv1, uu____71622)  in
                                      FStar_Syntax_Syntax.NT uu____71615  in
                                    [uu____71614]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___1717_71634 = b1  in
                                         let uu____71635 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___1717_71634.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___1717_71634.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____71635
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____71642  ->
                                       let new_goal =
                                         let uu____71644 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____71645 =
                                           let uu____71646 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____71646
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____71644 uu____71645
                                          in
                                       let uu____71647 = add_goals [new_goal]
                                          in
                                       bind uu____71647
                                         (fun uu____71652  ->
                                            let uu____71653 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv1.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____71653
                                              goal.FStar_Tactics_Types.opts
                                              goal.FStar_Tactics_Types.label))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____71513
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____71679 =
        let uu____71682 = cur_goal ()  in
        bind uu____71682
          (fun goal  ->
             let uu____71691 = b  in
             match uu____71691 with
             | (bv,uu____71695) ->
                 let uu____71700 =
                   let uu____71711 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____71711  in
                 (match uu____71700 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                      let steps =
                        let uu____71741 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____71741
                         in
                      let sort' =
                        normalize steps e0 bv1.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___1738_71746 = bv1  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___1738_71746.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___1738_71746.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____71748 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____71748))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____71679
  
let (revert : unit -> unit tac) =
  fun uu____71761  ->
    let uu____71764 = cur_goal ()  in
    bind uu____71764
      (fun goal  ->
         let uu____71770 =
           let uu____71777 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____71777  in
         match uu____71770 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____71794 =
                 let uu____71797 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____71797  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____71794
                in
             let uu____71812 = new_uvar "revert" env' typ'  in
             bind uu____71812
               (fun uu____71828  ->
                  match uu____71828 with
                  | (r,u_r) ->
                      let uu____71837 =
                        let uu____71840 =
                          let uu____71841 =
                            let uu____71842 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____71842.FStar_Syntax_Syntax.pos  in
                          let uu____71845 =
                            let uu____71850 =
                              let uu____71851 =
                                let uu____71860 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____71860  in
                              [uu____71851]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____71850  in
                          uu____71845 FStar_Pervasives_Native.None
                            uu____71841
                           in
                        set_solution goal uu____71840  in
                      bind uu____71837
                        (fun uu____71879  ->
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
      let uu____71893 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____71893
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____71909 = cur_goal ()  in
    bind uu____71909
      (fun goal  ->
         mlog
           (fun uu____71917  ->
              let uu____71918 = FStar_Syntax_Print.binder_to_string b  in
              let uu____71920 =
                let uu____71922 =
                  let uu____71924 =
                    let uu____71933 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____71933  in
                  FStar_All.pipe_right uu____71924 FStar_List.length  in
                FStar_All.pipe_right uu____71922 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____71918 uu____71920)
           (fun uu____71954  ->
              let uu____71955 =
                let uu____71966 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____71966  in
              match uu____71955 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bv1,bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____72011 =
                          free_in bv1 bv'.FStar_Syntax_Syntax.sort  in
                        if uu____72011
                        then
                          let uu____72016 =
                            let uu____72018 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____72018
                             in
                          fail uu____72016
                        else check1 bvs2
                     in
                  let uu____72023 =
                    let uu____72025 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv1 uu____72025  in
                  if uu____72023
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____72032 = check1 bvs  in
                     bind uu____72032
                       (fun uu____72038  ->
                          let env' = push_bvs e' bvs  in
                          let uu____72040 =
                            let uu____72047 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____72047  in
                          bind uu____72040
                            (fun uu____72057  ->
                               match uu____72057 with
                               | (ut,uvar_ut) ->
                                   let uu____72066 = set_solution goal ut  in
                                   bind uu____72066
                                     (fun uu____72071  ->
                                        let uu____72072 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                            goal.FStar_Tactics_Types.label
                                           in
                                        replace_cur uu____72072))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____72080  ->
    let uu____72083 = cur_goal ()  in
    bind uu____72083
      (fun goal  ->
         let uu____72089 =
           let uu____72096 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____72096  in
         match uu____72089 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____72105) ->
             let uu____72110 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____72110)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____72123 = cur_goal ()  in
    bind uu____72123
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____72133 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____72133  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____72136  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____72149 = cur_goal ()  in
    bind uu____72149
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____72159 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____72159  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____72162  -> add_goals [g']))
  
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
            let uu____72203 = FStar_Syntax_Subst.compress t  in
            uu____72203.FStar_Syntax_Syntax.n  in
          let uu____72206 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___1922_72213 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___1922_72213.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___1922_72213.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____72206
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____72230 =
                   let uu____72231 = FStar_Syntax_Subst.compress t1  in
                   uu____72231.FStar_Syntax_Syntax.n  in
                 match uu____72230 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____72262 = ff hd1  in
                     bind uu____72262
                       (fun hd2  ->
                          let fa uu____72288 =
                            match uu____72288 with
                            | (a,q) ->
                                let uu____72309 = ff a  in
                                bind uu____72309 (fun a1  -> ret (a1, q))
                             in
                          let uu____72328 = mapM fa args  in
                          bind uu____72328
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____72410 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____72410 with
                      | (bs1,t') ->
                          let uu____72419 =
                            let uu____72422 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____72422 t'  in
                          bind uu____72419
                            (fun t''  ->
                               let uu____72426 =
                                 let uu____72427 =
                                   let uu____72446 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____72455 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____72446, uu____72455, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____72427  in
                               ret uu____72426))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____72530 = ff hd1  in
                     bind uu____72530
                       (fun hd2  ->
                          let ffb br =
                            let uu____72545 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____72545 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____72577 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____72577  in
                                let uu____72578 = ff1 e  in
                                bind uu____72578
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____72593 = mapM ffb brs  in
                          bind uu____72593
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____72637;
                          FStar_Syntax_Syntax.lbtyp = uu____72638;
                          FStar_Syntax_Syntax.lbeff = uu____72639;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____72641;
                          FStar_Syntax_Syntax.lbpos = uu____72642;_}::[]),e)
                     ->
                     let lb =
                       let uu____72670 =
                         let uu____72671 = FStar_Syntax_Subst.compress t1  in
                         uu____72671.FStar_Syntax_Syntax.n  in
                       match uu____72670 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____72675) -> lb
                       | uu____72691 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____72701 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____72701
                         (fun def1  ->
                            ret
                              (let uu___1875_72707 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1875_72707.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1875_72707.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1875_72707.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1875_72707.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1875_72707.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1875_72707.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____72708 = fflb lb  in
                     bind uu____72708
                       (fun lb1  ->
                          let uu____72718 =
                            let uu____72723 =
                              let uu____72724 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____72724]  in
                            FStar_Syntax_Subst.open_term uu____72723 e  in
                          match uu____72718 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____72754 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____72754  in
                              let uu____72755 = ff1 e1  in
                              bind uu____72755
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____72802 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____72802
                         (fun def  ->
                            ret
                              (let uu___1893_72808 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1893_72808.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1893_72808.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1893_72808.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1893_72808.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1893_72808.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1893_72808.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____72809 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____72809 with
                      | (lbs1,e1) ->
                          let uu____72824 = mapM fflb lbs1  in
                          bind uu____72824
                            (fun lbs2  ->
                               let uu____72836 = ff e1  in
                               bind uu____72836
                                 (fun e2  ->
                                    let uu____72844 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____72844 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____72915 = ff t2  in
                     bind uu____72915
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____72946 = ff t2  in
                     bind uu____72946
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____72953 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___1917_72960 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___1917_72960.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___1917_72960.FStar_Syntax_Syntax.vars)
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
              let uu____73007 =
                FStar_TypeChecker_TcTerm.tc_term
                  (let uu___1930_73016 = env  in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___1930_73016.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___1930_73016.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___1930_73016.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___1930_73016.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_sig =
                       (uu___1930_73016.FStar_TypeChecker_Env.gamma_sig);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___1930_73016.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___1930_73016.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___1930_73016.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___1930_73016.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.attrtab =
                       (uu___1930_73016.FStar_TypeChecker_Env.attrtab);
                     FStar_TypeChecker_Env.is_pattern =
                       (uu___1930_73016.FStar_TypeChecker_Env.is_pattern);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___1930_73016.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___1930_73016.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___1930_73016.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___1930_73016.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___1930_73016.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___1930_73016.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___1930_73016.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___1930_73016.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___1930_73016.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax = true;
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___1930_73016.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.phase1 =
                       (uu___1930_73016.FStar_TypeChecker_Env.phase1);
                     FStar_TypeChecker_Env.failhard =
                       (uu___1930_73016.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___1930_73016.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.uvar_subtyping =
                       (uu___1930_73016.FStar_TypeChecker_Env.uvar_subtyping);
                     FStar_TypeChecker_Env.tc_term =
                       (uu___1930_73016.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.type_of =
                       (uu___1930_73016.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___1930_73016.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.check_type_of =
                       (uu___1930_73016.FStar_TypeChecker_Env.check_type_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___1930_73016.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (uu___1930_73016.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (uu___1930_73016.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.fv_delta_depths =
                       (uu___1930_73016.FStar_TypeChecker_Env.fv_delta_depths);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___1930_73016.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (uu___1930_73016.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.splice =
                       (uu___1930_73016.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.postprocess =
                       (uu___1930_73016.FStar_TypeChecker_Env.postprocess);
                     FStar_TypeChecker_Env.is_native_tactic =
                       (uu___1930_73016.FStar_TypeChecker_Env.is_native_tactic);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___1930_73016.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (uu___1930_73016.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (uu___1930_73016.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.nbe =
                       (uu___1930_73016.FStar_TypeChecker_Env.nbe)
                   }) t
                 in
              match uu____73007 with
              | (t1,lcomp,g) ->
                  let uu____73023 =
                    (let uu____73027 =
                       FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                     Prims.op_Negation uu____73027) ||
                      (let uu____73030 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____73030)
                     in
                  if uu____73023
                  then ret t1
                  else
                    (let rewrite_eq =
                       let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                       let uu____73041 = new_uvar "pointwise_rec" env typ  in
                       bind uu____73041
                         (fun uu____73058  ->
                            match uu____73058 with
                            | (ut,uvar_ut) ->
                                (log ps
                                   (fun uu____73071  ->
                                      let uu____73072 =
                                        FStar_Syntax_Print.term_to_string t1
                                         in
                                      let uu____73074 =
                                        FStar_Syntax_Print.term_to_string ut
                                         in
                                      FStar_Util.print2
                                        "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                        uu____73072 uu____73074);
                                 (let uu____73077 =
                                    let uu____73080 =
                                      let uu____73081 =
                                        FStar_TypeChecker_TcTerm.universe_of
                                          env typ
                                         in
                                      FStar_Syntax_Util.mk_eq2 uu____73081
                                        typ t1 ut
                                       in
                                    add_irrelevant_goal
                                      "pointwise_rec equation" env
                                      uu____73080 opts label1
                                     in
                                  bind uu____73077
                                    (fun uu____73085  ->
                                       let uu____73086 =
                                         bind tau
                                           (fun uu____73092  ->
                                              let ut1 =
                                                FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                  env ut
                                                 in
                                              log ps
                                                (fun uu____73098  ->
                                                   let uu____73099 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1
                                                      in
                                                   let uu____73101 =
                                                     FStar_Syntax_Print.term_to_string
                                                       ut1
                                                      in
                                                   FStar_Util.print2
                                                     "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                     uu____73099 uu____73101);
                                              ret ut1)
                                          in
                                       focus uu____73086))))
                        in
                     let uu____73104 = catch rewrite_eq  in
                     bind uu____73104
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
          let uu____73316 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____73316
            (fun t1  ->
               let uu____73324 =
                 f env
                   (let uu___2007_73332 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___2007_73332.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___2007_73332.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____73324
                 (fun uu____73348  ->
                    match uu____73348 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____73371 =
                               let uu____73372 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____73372.FStar_Syntax_Syntax.n  in
                             match uu____73371 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____73409 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____73409
                                   (fun uu____73431  ->
                                      match uu____73431 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____73447 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____73447
                                            (fun uu____73471  ->
                                               match uu____73471 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___1987_73501 =
                                                         t3  in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___1987_73501.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___1987_73501.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____73543 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____73543 with
                                  | (bs1,t') ->
                                      let uu____73558 =
                                        let uu____73565 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____73565 ctrl1 t'
                                         in
                                      bind uu____73558
                                        (fun uu____73580  ->
                                           match uu____73580 with
                                           | (t'',ctrl2) ->
                                               let uu____73595 =
                                                 let uu____73602 =
                                                   let uu___2000_73605 = t4
                                                      in
                                                   let uu____73608 =
                                                     let uu____73609 =
                                                       let uu____73628 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____73637 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____73628,
                                                         uu____73637, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____73609
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____73608;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___2000_73605.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___2000_73605.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____73602, ctrl2)  in
                                               ret uu____73595))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____73690 -> ret (t3, ctrl1))))

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
              let uu____73736 = ctrl_tac_fold f env ctrl t  in
              bind uu____73736
                (fun uu____73757  ->
                   match uu____73757 with
                   | (t1,ctrl1) ->
                       let uu____73772 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____73772
                         (fun uu____73796  ->
                            match uu____73796 with
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
                let uu____73887 =
                  let uu____73895 =
                    add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                      opts label1
                     in
                  bind uu____73895
                    (fun uu____73906  ->
                       let uu____73907 = ctrl t1  in
                       bind uu____73907
                         (fun res  ->
                            let uu____73933 = trivial ()  in
                            bind uu____73933 (fun uu____73942  -> ret res)))
                   in
                bind uu____73887
                  (fun uu____73960  ->
                     match uu____73960 with
                     | (should_rewrite,ctrl1) ->
                         if Prims.op_Negation should_rewrite
                         then ret (t1, ctrl1)
                         else
                           (let uu____73989 =
                              FStar_TypeChecker_TcTerm.tc_term
                                (let uu___2037_73998 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___2037_73998.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___2037_73998.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___2037_73998.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___2037_73998.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___2037_73998.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___2037_73998.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___2037_73998.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___2037_73998.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___2037_73998.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___2037_73998.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___2037_73998.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___2037_73998.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___2037_73998.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___2037_73998.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___2037_73998.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___2037_73998.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___2037_73998.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___2037_73998.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___2037_73998.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___2037_73998.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___2037_73998.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___2037_73998.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___2037_73998.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___2037_73998.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___2037_73998.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___2037_73998.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___2037_73998.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___2037_73998.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___2037_73998.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___2037_73998.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___2037_73998.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___2037_73998.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___2037_73998.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___2037_73998.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___2037_73998.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___2037_73998.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___2037_73998.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___2037_73998.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___2037_73998.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___2037_73998.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___2037_73998.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___2037_73998.FStar_TypeChecker_Env.nbe)
                                 }) t1
                               in
                            match uu____73989 with
                            | (t2,lcomp,g) ->
                                let uu____74009 =
                                  (let uu____74013 =
                                     FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                       lcomp
                                      in
                                   Prims.op_Negation uu____74013) ||
                                    (let uu____74016 =
                                       FStar_TypeChecker_Env.is_trivial g  in
                                     Prims.op_Negation uu____74016)
                                   in
                                if uu____74009
                                then ret (t2, globalStop)
                                else
                                  (let typ =
                                     lcomp.FStar_Syntax_Syntax.res_typ  in
                                   let uu____74032 =
                                     new_uvar "pointwise_rec" env typ  in
                                   bind uu____74032
                                     (fun uu____74053  ->
                                        match uu____74053 with
                                        | (ut,uvar_ut) ->
                                            (log ps
                                               (fun uu____74070  ->
                                                  let uu____74071 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t2
                                                     in
                                                  let uu____74073 =
                                                    FStar_Syntax_Print.term_to_string
                                                      ut
                                                     in
                                                  FStar_Util.print2
                                                    "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                    uu____74071 uu____74073);
                                             (let uu____74076 =
                                                let uu____74079 =
                                                  let uu____74080 =
                                                    FStar_TypeChecker_TcTerm.universe_of
                                                      env typ
                                                     in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____74080 typ t2 ut
                                                   in
                                                add_irrelevant_goal
                                                  "rewrite_rec equation" env
                                                  uu____74079 opts label1
                                                 in
                                              bind uu____74076
                                                (fun uu____74088  ->
                                                   let uu____74089 =
                                                     bind rewriter
                                                       (fun uu____74103  ->
                                                          let ut1 =
                                                            FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                              env ut
                                                             in
                                                          log ps
                                                            (fun uu____74109 
                                                               ->
                                                               let uu____74110
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   t2
                                                                  in
                                                               let uu____74112
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   ut1
                                                                  in
                                                               FStar_Util.print2
                                                                 "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                                 uu____74110
                                                                 uu____74112);
                                                          ret (ut1, ctrl1))
                                                      in
                                                   focus uu____74089)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term -> (Prims.bool * FStar_BigInt.t) tac) ->
    unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____74157 =
        bind get
          (fun ps  ->
             let uu____74167 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____74167 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____74205  ->
                       let uu____74206 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____74206);
                  bind dismiss_all
                    (fun uu____74211  ->
                       let uu____74212 =
                         let uu____74219 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____74219
                           keepGoing gt1
                          in
                       bind uu____74212
                         (fun uu____74229  ->
                            match uu____74229 with
                            | (gt',uu____74237) ->
                                (log ps
                                   (fun uu____74241  ->
                                      let uu____74242 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____74242);
                                 (let uu____74245 = push_goals gs  in
                                  bind uu____74245
                                    (fun uu____74250  ->
                                       let uu____74251 =
                                         let uu____74254 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____74254]  in
                                       add_goals uu____74251)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____74157
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____74279 =
        bind get
          (fun ps  ->
             let uu____74289 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____74289 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____74327  ->
                       let uu____74328 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____74328);
                  bind dismiss_all
                    (fun uu____74333  ->
                       let uu____74334 =
                         let uu____74337 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____74337 gt1
                          in
                       bind uu____74334
                         (fun gt'  ->
                            log ps
                              (fun uu____74345  ->
                                 let uu____74346 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____74346);
                            (let uu____74349 = push_goals gs  in
                             bind uu____74349
                               (fun uu____74354  ->
                                  let uu____74355 =
                                    let uu____74358 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____74358]  in
                                  add_goals uu____74355))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____74279
  
let (trefl : unit -> unit tac) =
  fun uu____74371  ->
    let uu____74374 =
      let uu____74377 = cur_goal ()  in
      bind uu____74377
        (fun g  ->
           let uu____74395 =
             let uu____74400 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____74400  in
           match uu____74395 with
           | FStar_Pervasives_Native.Some t ->
               let uu____74408 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____74408 with
                | (hd1,args) ->
                    let uu____74447 =
                      let uu____74460 =
                        let uu____74461 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____74461.FStar_Syntax_Syntax.n  in
                      (uu____74460, args)  in
                    (match uu____74447 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____74475::(l,uu____74477)::(r,uu____74479)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____74526 =
                           let uu____74530 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____74530 l r  in
                         bind uu____74526
                           (fun b  ->
                              if b
                              then solve' g FStar_Syntax_Util.exp_unit
                              else
                                (let l1 =
                                   let uu____74541 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____74541 l
                                    in
                                 let r1 =
                                   let uu____74543 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____74543 r
                                    in
                                 let uu____74544 =
                                   let uu____74548 =
                                     FStar_Tactics_Types.goal_env g  in
                                   do_unify uu____74548 l1 r1  in
                                 bind uu____74544
                                   (fun b1  ->
                                      if b1
                                      then
                                        solve' g FStar_Syntax_Util.exp_unit
                                      else
                                        (let uu____74558 =
                                           let uu____74560 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____74560 l1  in
                                         let uu____74561 =
                                           let uu____74563 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____74563 r1  in
                                         fail2
                                           "not a trivial equality ((%s) vs (%s))"
                                           uu____74558 uu____74561))))
                     | (hd2,uu____74566) ->
                         let uu____74583 =
                           let uu____74585 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____74585 t  in
                         fail1 "trefl: not an equality (%s)" uu____74583))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____74374
  
let (dup : unit -> unit tac) =
  fun uu____74602  ->
    let uu____74605 = cur_goal ()  in
    bind uu____74605
      (fun g  ->
         let uu____74611 =
           let uu____74618 = FStar_Tactics_Types.goal_env g  in
           let uu____74619 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____74618 uu____74619  in
         bind uu____74611
           (fun uu____74629  ->
              match uu____74629 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___2129_74639 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___2129_74639.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___2129_74639.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___2129_74639.FStar_Tactics_Types.is_guard);
                      FStar_Tactics_Types.label =
                        (uu___2129_74639.FStar_Tactics_Types.label)
                    }  in
                  bind __dismiss
                    (fun uu____74642  ->
                       let uu____74643 =
                         let uu____74646 = FStar_Tactics_Types.goal_env g  in
                         let uu____74647 =
                           let uu____74648 =
                             let uu____74649 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____74650 =
                               FStar_Tactics_Types.goal_type g  in
                             FStar_TypeChecker_TcTerm.universe_of uu____74649
                               uu____74650
                              in
                           let uu____74651 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____74652 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____74648 uu____74651 u
                             uu____74652
                            in
                         add_irrelevant_goal "dup equation" uu____74646
                           uu____74647 g.FStar_Tactics_Types.opts
                           g.FStar_Tactics_Types.label
                          in
                       bind uu____74643
                         (fun uu____74656  ->
                            let uu____74657 = add_goals [g']  in
                            bind uu____74657 (fun uu____74661  -> ret ())))))
  
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
              let uu____74787 = f x y  in
              if uu____74787 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____74810 -> (acc, l11, l21)  in
        let uu____74825 = aux [] l1 l2  in
        match uu____74825 with | (pr,t1,t2) -> ((FStar_List.rev pr), t1, t2)
  
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
      let uu____74931 = get_phi g1  in
      match uu____74931 with
      | FStar_Pervasives_Native.None  -> fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____74938 = get_phi g2  in
          (match uu____74938 with
           | FStar_Pervasives_Native.None  -> fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let uu____74951 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2)
                  in
               (match uu____74951 with
                | (gamma,r1,r2) ->
                    let t1 =
                      let uu____74982 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1)
                         in
                      close_forall_no_univs1 uu____74982 phi1  in
                    let t2 =
                      let uu____74992 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2)
                         in
                      close_forall_no_univs1 uu____74992 phi2  in
                    let uu____75001 =
                      set_solution g1 FStar_Syntax_Util.exp_unit  in
                    bind uu____75001
                      (fun uu____75006  ->
                         let uu____75007 =
                           set_solution g2 FStar_Syntax_Util.exp_unit  in
                         bind uu____75007
                           (fun uu____75014  ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2  in
                              let nenv =
                                let uu___2180_75019 =
                                  FStar_Tactics_Types.goal_env g1  in
                                let uu____75020 =
                                  FStar_Util.smap_create
                                    (Prims.parse_int "100")
                                   in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___2180_75019.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___2180_75019.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___2180_75019.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___2180_75019.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____75020;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___2180_75019.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___2180_75019.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___2180_75019.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___2180_75019.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___2180_75019.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___2180_75019.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___2180_75019.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___2180_75019.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___2180_75019.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___2180_75019.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___2180_75019.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___2180_75019.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___2180_75019.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___2180_75019.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___2180_75019.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___2180_75019.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___2180_75019.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___2180_75019.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___2180_75019.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___2180_75019.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___2180_75019.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___2180_75019.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___2180_75019.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___2180_75019.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___2180_75019.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___2180_75019.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___2180_75019.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___2180_75019.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___2180_75019.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___2180_75019.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___2180_75019.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___2180_75019.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___2180_75019.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___2180_75019.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___2180_75019.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___2180_75019.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___2180_75019.FStar_TypeChecker_Env.nbe)
                                }  in
                              let uu____75024 =
                                mk_irrelevant_goal "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                  g1.FStar_Tactics_Types.label
                                 in
                              bind uu____75024
                                (fun goal  ->
                                   mlog
                                     (fun uu____75034  ->
                                        let uu____75035 =
                                          goal_to_string_verbose g1  in
                                        let uu____75037 =
                                          goal_to_string_verbose g2  in
                                        let uu____75039 =
                                          goal_to_string_verbose goal  in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____75035 uu____75037 uu____75039)
                                     (fun uu____75043  -> ret goal))))))
  
let (join : unit -> unit tac) =
  fun uu____75051  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____75067 =
               set
                 (let uu___2195_75072 = ps  in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___2195_75072.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.main_goal =
                      (uu___2195_75072.FStar_Tactics_Types.main_goal);
                    FStar_Tactics_Types.all_implicits =
                      (uu___2195_75072.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___2195_75072.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___2195_75072.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___2195_75072.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___2195_75072.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___2195_75072.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___2195_75072.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___2195_75072.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___2195_75072.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___2195_75072.FStar_Tactics_Types.local_state)
                  })
                in
             bind uu____75067
               (fun uu____75075  ->
                  let uu____75076 = join_goals g1 g2  in
                  bind uu____75076 (fun g12  -> add_goals [g12]))
         | uu____75081 -> fail "join: less than 2 goals")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) tac)
  =
  fun t  ->
    let uu____75103 =
      let uu____75110 = cur_goal ()  in
      bind uu____75110
        (fun g  ->
           let uu____75120 =
             let uu____75129 = FStar_Tactics_Types.goal_env g  in
             __tc uu____75129 t  in
           bind uu____75120
             (fun uu____75157  ->
                match uu____75157 with
                | (t1,typ,guard) ->
                    let uu____75173 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____75173 with
                     | (hd1,args) ->
                         let uu____75222 =
                           let uu____75237 =
                             let uu____75238 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____75238.FStar_Syntax_Syntax.n  in
                           (uu____75237, args)  in
                         (match uu____75222 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____75259)::(q,uu____75261)::[]) when
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
                                let uu____75315 =
                                  let uu____75316 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____75316
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____75315
                                 in
                              let g2 =
                                let uu____75318 =
                                  let uu____75319 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____75319
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____75318
                                 in
                              bind __dismiss
                                (fun uu____75326  ->
                                   let uu____75327 = add_goals [g1; g2]  in
                                   bind uu____75327
                                     (fun uu____75336  ->
                                        let uu____75337 =
                                          let uu____75342 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____75343 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____75342, uu____75343)  in
                                        ret uu____75337))
                          | uu____75348 ->
                              let uu____75363 =
                                let uu____75365 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____75365 typ  in
                              fail1 "Not a disjunction: %s" uu____75363))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____75103
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____75400 =
      let uu____75403 = cur_goal ()  in
      bind uu____75403
        (fun g  ->
           FStar_Options.push ();
           (let uu____75416 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____75416);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___2232_75423 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___2232_75423.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___2232_75423.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___2232_75423.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___2232_75423.FStar_Tactics_Types.label)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____75400
  
let (top_env : unit -> env tac) =
  fun uu____75440  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____75455  ->
    let uu____75459 = cur_goal ()  in
    bind uu____75459
      (fun g  ->
         let uu____75466 =
           (FStar_Options.lax ()) ||
             (let uu____75469 = FStar_Tactics_Types.goal_env g  in
              uu____75469.FStar_TypeChecker_Env.lax)
            in
         ret uu____75466)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____75486 =
        mlog
          (fun uu____75491  ->
             let uu____75492 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____75492)
          (fun uu____75497  ->
             let uu____75498 = cur_goal ()  in
             bind uu____75498
               (fun goal  ->
                  let env =
                    let uu____75506 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____75506 ty  in
                  let uu____75507 = __tc_ghost env tm  in
                  bind uu____75507
                    (fun uu____75526  ->
                       match uu____75526 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____75540  ->
                                let uu____75541 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____75541)
                             (fun uu____75545  ->
                                mlog
                                  (fun uu____75548  ->
                                     let uu____75549 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____75549)
                                  (fun uu____75554  ->
                                     let uu____75555 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____75555
                                       (fun uu____75560  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____75486
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____75585 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____75591 =
              let uu____75598 =
                let uu____75599 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____75599
                 in
              new_uvar "uvar_env.2" env uu____75598  in
            bind uu____75591
              (fun uu____75616  ->
                 match uu____75616 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____75585
        (fun typ  ->
           let uu____75628 = new_uvar "uvar_env" env typ  in
           bind uu____75628
             (fun uu____75643  ->
                match uu____75643 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____75662 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____75681 -> g.FStar_Tactics_Types.opts
             | uu____75684 -> FStar_Options.peek ()  in
           let uu____75687 = FStar_Syntax_Util.head_and_args t  in
           match uu____75687 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____75707);
                FStar_Syntax_Syntax.pos = uu____75708;
                FStar_Syntax_Syntax.vars = uu____75709;_},uu____75710)
               ->
               let env1 =
                 let uu___2286_75752 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___2286_75752.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___2286_75752.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___2286_75752.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___2286_75752.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___2286_75752.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___2286_75752.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___2286_75752.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___2286_75752.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___2286_75752.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___2286_75752.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___2286_75752.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___2286_75752.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___2286_75752.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___2286_75752.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___2286_75752.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___2286_75752.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___2286_75752.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___2286_75752.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___2286_75752.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___2286_75752.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___2286_75752.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___2286_75752.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___2286_75752.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___2286_75752.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___2286_75752.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___2286_75752.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___2286_75752.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___2286_75752.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___2286_75752.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___2286_75752.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___2286_75752.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___2286_75752.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___2286_75752.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___2286_75752.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___2286_75752.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___2286_75752.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___2286_75752.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___2286_75752.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___2286_75752.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___2286_75752.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___2286_75752.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___2286_75752.FStar_TypeChecker_Env.nbe)
                 }  in
               let g =
                 FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false ""  in
               let uu____75756 =
                 let uu____75759 = bnorm_goal g  in [uu____75759]  in
               add_goals uu____75756
           | uu____75760 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____75662
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____75822 = if b then t2 else ret false  in
             bind uu____75822 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____75848 = trytac comp  in
      bind uu____75848
        (fun uu___613_75860  ->
           match uu___613_75860 with
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
        let uu____75902 =
          bind get
            (fun ps  ->
               let uu____75910 = __tc e t1  in
               bind uu____75910
                 (fun uu____75931  ->
                    match uu____75931 with
                    | (t11,ty1,g1) ->
                        let uu____75944 = __tc e t2  in
                        bind uu____75944
                          (fun uu____75965  ->
                             match uu____75965 with
                             | (t21,ty2,g2) ->
                                 let uu____75978 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____75978
                                   (fun uu____75985  ->
                                      let uu____75986 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____75986
                                        (fun uu____75994  ->
                                           let uu____75995 =
                                             do_unify e ty1 ty2  in
                                           let uu____75999 =
                                             do_unify e t11 t21  in
                                           tac_and uu____75995 uu____75999)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____75902
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____76047  ->
             let uu____76048 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____76048
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
        (fun uu____76082  ->
           let uu____76083 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____76083)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____76094 =
      mlog
        (fun uu____76099  ->
           let uu____76100 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____76100)
        (fun uu____76105  ->
           let uu____76106 = cur_goal ()  in
           bind uu____76106
             (fun g  ->
                let uu____76112 =
                  let uu____76121 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____76121 ty  in
                bind uu____76112
                  (fun uu____76133  ->
                     match uu____76133 with
                     | (ty1,uu____76143,guard) ->
                         let uu____76145 =
                           let uu____76148 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____76148 guard  in
                         bind uu____76145
                           (fun uu____76152  ->
                              let uu____76153 =
                                let uu____76157 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____76158 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____76157 uu____76158 ty1  in
                              bind uu____76153
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____76167 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____76167
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops]  in
                                      let ng =
                                        let uu____76174 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____76175 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____76174
                                          uu____76175
                                         in
                                      let nty =
                                        let uu____76177 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____76177 ty1  in
                                      let uu____76178 =
                                        let uu____76182 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____76182 ng nty  in
                                      bind uu____76178
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____76191 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____76191
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____76094
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) Prims.list tac)
  =
  fun s_tm  ->
    let uu____76265 =
      let uu____76274 = cur_goal ()  in
      bind uu____76274
        (fun g  ->
           let uu____76286 =
             let uu____76295 = FStar_Tactics_Types.goal_env g  in
             __tc uu____76295 s_tm  in
           bind uu____76286
             (fun uu____76313  ->
                match uu____76313 with
                | (s_tm1,s_ty,guard) ->
                    let uu____76331 =
                      let uu____76334 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____76334 guard  in
                    bind uu____76331
                      (fun uu____76347  ->
                         let uu____76348 =
                           FStar_Syntax_Util.head_and_args' s_ty  in
                         match uu____76348 with
                         | (h,args) ->
                             let uu____76393 =
                               let uu____76400 =
                                 let uu____76401 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____76401.FStar_Syntax_Syntax.n  in
                               match uu____76400 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____76416;
                                      FStar_Syntax_Syntax.vars = uu____76417;_},us)
                                   -> ret (fv, us)
                               | uu____76427 -> fail "type is not an fv"  in
                             bind uu____76393
                               (fun uu____76448  ->
                                  match uu____76448 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____76464 =
                                        let uu____76467 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____76467 t_lid
                                         in
                                      (match uu____76464 with
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
                                                  (fun uu____76518  ->
                                                     let uu____76519 =
                                                       FStar_Syntax_Subst.open_term
                                                         t_ps t_ty
                                                        in
                                                     match uu____76519 with
                                                     | (t_ps1,t_ty1) ->
                                                         let uu____76534 =
                                                           mapM
                                                             (fun c_lid  ->
                                                                let uu____76562
                                                                  =
                                                                  let uu____76565
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                  FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____76565
                                                                    c_lid
                                                                   in
                                                                match uu____76562
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
                                                                    uu____76639
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
                                                                    let uu____76644
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____76644
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____76667
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____76667
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____76710
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs
                                                                     in
                                                                    (match uu____76710
                                                                    with
                                                                    | 
                                                                    (d_ps,bs1)
                                                                    ->
                                                                    let uu____76783
                                                                    =
                                                                    let uu____76785
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp  in
                                                                    Prims.op_Negation
                                                                    uu____76785
                                                                     in
                                                                    failwhen
                                                                    uu____76783
                                                                    "not total?"
                                                                    (fun
                                                                    uu____76804
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
                                                                    uu___614_76821
                                                                    =
                                                                    match uu___614_76821
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____76825)
                                                                    -> true
                                                                    | 
                                                                    uu____76828
                                                                    -> false
                                                                     in
                                                                    let uu____76832
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____76832
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
                                                                    uu____76966
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
                                                                    uu____77028
                                                                     ->
                                                                    match uu____77028
                                                                    with
                                                                    | 
                                                                    ((bv,uu____77048),
                                                                    (t,uu____77050))
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
                                                                    uu____77120
                                                                     ->
                                                                    match uu____77120
                                                                    with
                                                                    | 
                                                                    ((bv,uu____77147),
                                                                    (t,uu____77149))
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
                                                                    uu____77208
                                                                     ->
                                                                    match uu____77208
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
                                                                    let uu____77263
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___2450_77280
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___2450_77280.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___2450_77280.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___2450_77280.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___2450_77280.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___2450_77280.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___2450_77280.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___2450_77280.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___2450_77280.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___2450_77280.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___2450_77280.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___2450_77280.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___2450_77280.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___2450_77280.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___2450_77280.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___2450_77280.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___2450_77280.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___2450_77280.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___2450_77280.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___2450_77280.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___2450_77280.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___2450_77280.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___2450_77280.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___2450_77280.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___2450_77280.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___2450_77280.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___2450_77280.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___2450_77280.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___2450_77280.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___2450_77280.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___2450_77280.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___2450_77280.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___2450_77280.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___2450_77280.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___2450_77280.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___2450_77280.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___2450_77280.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___2450_77280.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___2450_77280.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___2450_77280.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___2450_77280.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___2450_77280.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___2450_77280.FStar_TypeChecker_Env.nbe)
                                                                    }) s_ty
                                                                    pat  in
                                                                    match uu____77263
                                                                    with
                                                                    | 
                                                                    (uu____77294,uu____77295,uu____77296,pat_t,uu____77298,_guard_pat)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____77305
                                                                    =
                                                                    let uu____77306
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____77306
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____77305
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____77311
                                                                    =
                                                                    let uu____77320
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____77320]
                                                                     in
                                                                    let uu____77339
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____77311
                                                                    uu____77339
                                                                     in
                                                                    let nty =
                                                                    let uu____77345
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____77345
                                                                     in
                                                                    let uu____77348
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____77348
                                                                    (fun
                                                                    uu____77378
                                                                     ->
                                                                    match uu____77378
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
                                                                    let uu____77405
                                                                    =
                                                                    let uu____77416
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____77416]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____77405
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____77452
                                                                    =
                                                                    let uu____77463
                                                                    =
                                                                    let uu____77468
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2)  in
                                                                    (fv1,
                                                                    uu____77468)
                                                                     in
                                                                    (g', br,
                                                                    uu____77463)
                                                                     in
                                                                    ret
                                                                    uu____77452))))))
                                                                    | 
                                                                    uu____77489
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                             c_lids
                                                            in
                                                         bind uu____76534
                                                           (fun goal_brs  ->
                                                              let uu____77539
                                                                =
                                                                FStar_List.unzip3
                                                                  goal_brs
                                                                 in
                                                              match uu____77539
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
                                                                  let uu____77612
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                  bind
                                                                    uu____77612
                                                                    (
                                                                    fun
                                                                    uu____77623
                                                                     ->
                                                                    let uu____77624
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____77624
                                                                    (fun
                                                                    uu____77634
                                                                     ->
                                                                    ret infos))))
                                            | uu____77641 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____76265
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____77690::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____77720 = init xs  in x :: uu____77720
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____77733 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      let t3 = FStar_Syntax_Util.unlazy_emb t2  in
      match t3.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____77742) -> inspect t4
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____77808 = last args  in
          (match uu____77808 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____77838 =
                 let uu____77839 =
                   let uu____77844 =
                     let uu____77845 =
                       let uu____77850 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____77850  in
                     uu____77845 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____77844, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____77839  in
               FStar_All.pipe_left ret uu____77838)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____77861,uu____77862) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
          let uu____77915 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____77915 with
           | (bs1,t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____77957 =
                      let uu____77958 =
                        let uu____77963 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____77963)  in
                      FStar_Reflection_Data.Tv_Abs uu____77958  in
                    FStar_All.pipe_left ret uu____77957))
      | FStar_Syntax_Syntax.Tm_type uu____77966 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____77991 ->
          let uu____78006 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____78006 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____78037 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____78037 with
           | (b',t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____78090 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____78103 =
            let uu____78104 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____78104  in
          FStar_All.pipe_left ret uu____78103
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____78125 =
            let uu____78126 =
              let uu____78131 =
                let uu____78132 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____78132  in
              (uu____78131, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____78126  in
          FStar_All.pipe_left ret uu____78125
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____78172 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____78177 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____78177 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____78230 ->
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
             | FStar_Util.Inr uu____78272 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____78276 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____78276 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____78296 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____78302 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____78357 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____78357
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____78378 =
                  let uu____78385 =
                    FStar_List.map
                      (fun uu____78398  ->
                         match uu____78398 with
                         | (p1,uu____78407) -> inspect_pat p1) ps
                     in
                  (fv, uu____78385)  in
                FStar_Reflection_Data.Pat_Cons uu____78378
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
              (fun uu___615_78503  ->
                 match uu___615_78503 with
                 | (pat,uu____78525,t5) ->
                     let uu____78543 = inspect_pat pat  in (uu____78543, t5))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____78552 ->
          ((let uu____78554 =
              let uu____78560 =
                let uu____78562 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____78564 = FStar_Syntax_Print.term_to_string t3  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____78562 uu____78564
                 in
              (FStar_Errors.Warning_CantInspect, uu____78560)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____78554);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____77733
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____78582 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____78582
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____78586 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____78586
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____78590 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____78590
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____78597 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____78597
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____78622 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____78622
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____78639 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____78639
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____78658 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____78658
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____78662 =
          let uu____78663 =
            let uu____78670 =
              let uu____78671 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____78671  in
            FStar_Syntax_Syntax.mk uu____78670  in
          uu____78663 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____78662
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____78676 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____78676
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____78687 =
          let uu____78688 =
            let uu____78695 =
              let uu____78696 =
                let uu____78710 =
                  let uu____78713 =
                    let uu____78714 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____78714]  in
                  FStar_Syntax_Subst.close uu____78713 t2  in
                ((false, [lb]), uu____78710)  in
              FStar_Syntax_Syntax.Tm_let uu____78696  in
            FStar_Syntax_Syntax.mk uu____78695  in
          uu____78688 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____78687
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____78756 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____78756 with
         | (lbs,body) ->
             let uu____78771 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____78771)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____78808 =
                let uu____78809 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____78809  in
              FStar_All.pipe_left wrap uu____78808
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____78816 =
                let uu____78817 =
                  let uu____78831 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____78849 = pack_pat p1  in
                         (uu____78849, false)) ps
                     in
                  (fv, uu____78831)  in
                FStar_Syntax_Syntax.Pat_cons uu____78817  in
              FStar_All.pipe_left wrap uu____78816
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
            (fun uu___616_78898  ->
               match uu___616_78898 with
               | (pat,t1) ->
                   let uu____78915 = pack_pat pat  in
                   (uu____78915, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____78963 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____78963
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____78991 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____78991
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____79037 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____79037
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____79076 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____79076
  
let (lget :
  FStar_Reflection_Data.typ -> Prims.string -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun k  ->
      let uu____79096 =
        bind get
          (fun ps  ->
             let uu____79102 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____79102 with
             | FStar_Pervasives_Native.None  -> fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
      FStar_All.pipe_left (wrap_err "lget") uu____79096
  
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit tac)
  =
  fun _ty  ->
    fun k  ->
      fun t  ->
        let uu____79136 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___2748_79143 = ps  in
                 let uu____79144 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t
                    in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___2748_79143.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___2748_79143.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___2748_79143.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___2748_79143.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___2748_79143.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___2748_79143.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___2748_79143.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___2748_79143.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___2748_79143.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___2748_79143.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___2748_79143.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___2748_79143.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____79144
                 }  in
               set ps1)
           in
        FStar_All.pipe_left (wrap_err "lset") uu____79136
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal * FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun typ  ->
      let uu____79171 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____79171 with
      | (u,ctx_uvars,g_u) ->
          let uu____79204 = FStar_List.hd ctx_uvars  in
          (match uu____79204 with
           | (ctx_uvar,uu____79218) ->
               let g =
                 let uu____79220 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____79220 false
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
        let uu____79243 = goal_of_goal_ty env typ  in
        match uu____79243 with
        | (g,g_u) ->
            let ps =
              let uu____79255 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "TacVerbose")
                 in
              let uu____79258 = FStar_Util.psmap_empty ()  in
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
                FStar_Tactics_Types.tac_verb_dbg = uu____79255;
                FStar_Tactics_Types.local_state = uu____79258
              }  in
            let uu____79268 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____79268)
  