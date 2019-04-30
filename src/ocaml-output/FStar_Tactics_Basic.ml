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
    let uu____44 =
      let uu____45 = FStar_Tactics_Types.goal_env g  in
      let uu____46 = FStar_Tactics_Types.goal_type g  in
      bnorm uu____45 uu____46  in
    FStar_Tactics_Types.goal_with_type g uu____44
  
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
      let uu____160 = FStar_Options.tactics_failhard ()  in
      if uu____160
      then run t p
      else
        (try (fun uu___31_170  -> match () with | () -> run t p) ()
         with
         | FStar_Errors.Err (uu____179,msg) ->
             FStar_Tactics_Result.Failed
               ((FStar_Tactics_Types.TacticFailure msg), p)
         | FStar_Errors.Error (uu____183,msg,uu____185) ->
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
           let uu____265 = run t1 p  in
           match uu____265 with
           | FStar_Tactics_Result.Success (a,q) ->
               let uu____272 = t2 a  in run uu____272 q
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
    let uu____295 =
      FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head  in
    match uu____295 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (check_goal_solved :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun goal  -> get_uvar_solved goal.FStar_Tactics_Types.goal_ctx_uvar 
let (goal_to_string_verbose : FStar_Tactics_Types.goal -> Prims.string) =
  fun g  ->
    let uu____317 =
      FStar_Syntax_Print.ctx_uvar_to_string
        g.FStar_Tactics_Types.goal_ctx_uvar
       in
    let uu____319 =
      let uu____321 = check_goal_solved g  in
      match uu____321 with
      | FStar_Pervasives_Native.None  -> ""
      | FStar_Pervasives_Native.Some t ->
          let uu____327 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "\tGOAL ALREADY SOLVED!: %s" uu____327
       in
    FStar_Util.format2 "%s%s\n" uu____317 uu____319
  
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
            let uu____374 = FStar_Options.print_implicits ()  in
            if uu____374
            then
              let uu____378 = FStar_Tactics_Types.goal_env g  in
              let uu____379 = FStar_Tactics_Types.goal_witness g  in
              tts uu____378 uu____379
            else
              (let uu____382 =
                 get_uvar_solved g.FStar_Tactics_Types.goal_ctx_uvar  in
               match uu____382 with
               | FStar_Pervasives_Native.None  -> "_"
               | FStar_Pervasives_Native.Some t ->
                   let uu____388 = FStar_Tactics_Types.goal_env g  in
                   let uu____389 = FStar_Tactics_Types.goal_witness g  in
                   tts uu____388 uu____389)
             in
          let num =
            match maybe_num with
            | FStar_Pervasives_Native.None  -> ""
            | FStar_Pervasives_Native.Some (i,n1) ->
                let uu____412 = FStar_Util.string_of_int i  in
                let uu____414 = FStar_Util.string_of_int n1  in
                FStar_Util.format2 " %s/%s" uu____412 uu____414
             in
          let maybe_label =
            match g.FStar_Tactics_Types.label with
            | "" -> ""
            | l -> Prims.op_Hat " (" (Prims.op_Hat l ")")  in
          let actual_goal =
            if ps.FStar_Tactics_Types.tac_verb_dbg
            then goal_to_string_verbose g
            else
              (let uu____432 =
                 FStar_Syntax_Print.binders_to_string ", "
                   (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
                  in
               let uu____435 =
                 let uu____437 = FStar_Tactics_Types.goal_env g  in
                 tts uu____437
                   (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                  in
               FStar_Util.format3 "%s |- %s : %s\n" uu____432 w uu____435)
             in
          FStar_Util.format4 "%s%s%s:\n%s\n" kind num maybe_label actual_goal
  
let (tacprint : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      let uu____464 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____464
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____489 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____489
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____521 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____521
  
let (get_phi :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun g  ->
    let uu____534 =
      let uu____535 = FStar_Tactics_Types.goal_env g  in
      let uu____536 = FStar_Tactics_Types.goal_type g  in
      FStar_TypeChecker_Normalize.unfold_whnf uu____535 uu____536  in
    FStar_Syntax_Util.un_squash uu____534
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  -> let uu____545 = get_phi g  in FStar_Option.isSome uu____545 
let (print : Prims.string -> unit tac) = fun msg  -> tacprint msg; ret () 
let (debugging : unit -> Prims.bool tac) =
  fun uu____569  ->
    bind get
      (fun ps  ->
         let uu____577 =
           FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
             (FStar_Options.Other "Tac")
            in
         ret uu____577)
  
let (ps_to_string :
  (Prims.string * FStar_Tactics_Types.proofstate) -> Prims.string) =
  fun uu____592  ->
    match uu____592 with
    | (msg,ps) ->
        let p_imp imp =
          FStar_Syntax_Print.uvar_to_string
            (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
           in
        let n_active = FStar_List.length ps.FStar_Tactics_Types.goals  in
        let n_smt = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
        let n1 = n_active + n_smt  in
        let uu____614 =
          let uu____618 =
            let uu____622 =
              let uu____624 =
                FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
              FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____624
                msg
               in
            let uu____627 =
              let uu____631 =
                if
                  ps.FStar_Tactics_Types.entry_range <>
                    FStar_Range.dummyRange
                then
                  let uu____635 =
                    FStar_Range.string_of_def_range
                      ps.FStar_Tactics_Types.entry_range
                     in
                  FStar_Util.format1 "Location: %s\n" uu____635
                else ""  in
              let uu____641 =
                let uu____645 =
                  let uu____647 =
                    FStar_TypeChecker_Env.debug
                      ps.FStar_Tactics_Types.main_context
                      (FStar_Options.Other "Imp")
                     in
                  if uu____647
                  then
                    let uu____652 =
                      FStar_Common.string_of_list p_imp
                        ps.FStar_Tactics_Types.all_implicits
                       in
                    FStar_Util.format1 "Imps: %s\n" uu____652
                  else ""  in
                [uu____645]  in
              uu____631 :: uu____641  in
            uu____622 :: uu____627  in
          let uu____662 =
            let uu____666 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "Goal"
                       (FStar_Pervasives_Native.Some
                          (((Prims.parse_int "1") + i), n1)) ps g)
                ps.FStar_Tactics_Types.goals
               in
            let uu____686 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "SMT Goal"
                       (FStar_Pervasives_Native.Some
                          ((((Prims.parse_int "1") + n_active) + i), n1)) ps
                       g) ps.FStar_Tactics_Types.smt_goals
               in
            FStar_List.append uu____666 uu____686  in
          FStar_List.append uu____618 uu____662  in
        FStar_String.concat "" uu____614
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      let uu____716 =
        let uu____717 = FStar_Tactics_Types.goal_env g  in
        FStar_TypeChecker_Env.all_binders uu____717  in
      let uu____718 =
        let uu____723 =
          let uu____724 = FStar_Tactics_Types.goal_env g  in
          FStar_TypeChecker_Env.dsenv uu____724  in
        FStar_Syntax_Print.binders_to_json uu____723  in
      FStar_All.pipe_right uu____716 uu____718  in
    let uu____725 =
      let uu____733 =
        let uu____741 =
          let uu____747 =
            let uu____748 =
              let uu____756 =
                let uu____762 =
                  let uu____763 =
                    let uu____765 = FStar_Tactics_Types.goal_env g  in
                    let uu____766 = FStar_Tactics_Types.goal_witness g  in
                    tts uu____765 uu____766  in
                  FStar_Util.JsonStr uu____763  in
                ("witness", uu____762)  in
              let uu____769 =
                let uu____777 =
                  let uu____783 =
                    let uu____784 =
                      let uu____786 = FStar_Tactics_Types.goal_env g  in
                      let uu____787 = FStar_Tactics_Types.goal_type g  in
                      tts uu____786 uu____787  in
                    FStar_Util.JsonStr uu____784  in
                  ("type", uu____783)  in
                [uu____777;
                ("label", (FStar_Util.JsonStr (g.FStar_Tactics_Types.label)))]
                 in
              uu____756 :: uu____769  in
            FStar_Util.JsonAssoc uu____748  in
          ("goal", uu____747)  in
        [uu____741]  in
      ("hyps", g_binders) :: uu____733  in
    FStar_Util.JsonAssoc uu____725
  
let (ps_to_json :
  (Prims.string * FStar_Tactics_Types.proofstate) -> FStar_Util.json) =
  fun uu____841  ->
    match uu____841 with
    | (msg,ps) ->
        let uu____851 =
          let uu____859 =
            let uu____867 =
              let uu____875 =
                let uu____883 =
                  let uu____889 =
                    let uu____890 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____890  in
                  ("goals", uu____889)  in
                let uu____895 =
                  let uu____903 =
                    let uu____909 =
                      let uu____910 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____910  in
                    ("smt-goals", uu____909)  in
                  [uu____903]  in
                uu____883 :: uu____895  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____875
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____867  in
          let uu____944 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____960 =
                let uu____966 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____966)  in
              [uu____960]
            else []  in
          FStar_List.append uu____859 uu____944  in
        FStar_Util.JsonAssoc uu____851
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____1006  ->
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
         (let uu____1037 = FStar_Tactics_Types.subst_proof_state subst1 ps
             in
          dump_proofstate uu____1037 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let traise : 'a . Prims.exn -> 'a tac =
  fun e  -> mk_tac (fun ps  -> FStar_Tactics_Result.Failed (e, ps)) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____1110 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____1110
          then dump_proofstate ps (Prims.op_Hat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed
           ((FStar_Tactics_Types.TacticFailure msg), ps))
  
let fail1 : 'Auu____1124 . Prims.string -> Prims.string -> 'Auu____1124 tac =
  fun msg  ->
    fun x  -> let uu____1141 = FStar_Util.format1 msg x  in fail uu____1141
  
let fail2 :
  'Auu____1152 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____1152 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        let uu____1176 = FStar_Util.format2 msg x y  in fail uu____1176
  
let fail3 :
  'Auu____1189 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____1189 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____1220 = FStar_Util.format3 msg x y z  in fail uu____1220
  
let fail4 :
  'Auu____1235 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____1235 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____1273 = FStar_Util.format4 msg x y z w  in
            fail uu____1273
  
let catch : 'a . 'a tac -> (Prims.exn,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____1308 = run t ps  in
         match uu____1308 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___183_1332 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___183_1332.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___183_1332.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___183_1332.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___183_1332.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___183_1332.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___183_1332.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___183_1332.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___183_1332.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___183_1332.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___183_1332.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___183_1332.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (uu___183_1332.FStar_Tactics_Types.local_state)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let recover : 'a . 'a tac -> (Prims.exn,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let uu____1371 = run t ps  in
         match uu____1371 with
         | FStar_Tactics_Result.Success (a,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inr a), q)
         | FStar_Tactics_Result.Failed (m,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inl m), q))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____1419 = catch t  in
    bind uu____1419
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____1446 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try
           (fun uu___209_1478  ->
              match () with
              | () -> let uu____1483 = trytac t  in run uu____1483 ps) ()
         with
         | FStar_Errors.Err (uu____1499,msg) ->
             (log ps
                (fun uu____1505  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____1511,msg,uu____1513) ->
             (log ps
                (fun uu____1518  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____1555 = run t ps  in
           match uu____1555 with
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
  fun p  -> mk_tac (fun uu____1579  -> FStar_Tactics_Result.Success ((), p)) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___244_1594 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___244_1594.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___244_1594.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___244_1594.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___244_1594.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___244_1594.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___244_1594.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___244_1594.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___244_1594.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___244_1594.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___244_1594.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___244_1594.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___244_1594.FStar_Tactics_Types.local_state)
            }))
  
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____1618 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____1618
         then
           let uu____1622 = FStar_Syntax_Print.term_to_string t1  in
           let uu____1624 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____1622
             uu____1624
         else ());
        (try
           (fun uu___252_1635  ->
              match () with
              | () ->
                  let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
                  ((let uu____1643 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1643
                    then
                      let uu____1647 =
                        FStar_Common.string_of_option
                          (FStar_TypeChecker_Rel.guard_to_string env) res
                         in
                      let uu____1649 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____1651 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.print3
                        "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____1647
                        uu____1649 uu____1651
                    else ());
                   (match res with
                    | FStar_Pervasives_Native.None  -> ret false
                    | FStar_Pervasives_Native.Some g ->
                        let uu____1662 =
                          add_implicits g.FStar_TypeChecker_Env.implicits  in
                        bind uu____1662 (fun uu____1667  -> ret true)))) ()
         with
         | FStar_Errors.Err (uu____1677,msg) ->
             mlog
               (fun uu____1683  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____1686  -> ret false)
         | FStar_Errors.Error (uu____1689,msg,r) ->
             mlog
               (fun uu____1697  ->
                  let uu____1698 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____1698) (fun uu____1702  -> ret false))
  
let (compress_implicits : unit tac) =
  bind get
    (fun ps  ->
       let imps = ps.FStar_Tactics_Types.all_implicits  in
       let g =
         let uu___278_1716 = FStar_TypeChecker_Env.trivial_guard  in
         {
           FStar_TypeChecker_Env.guard_f =
             (uu___278_1716.FStar_TypeChecker_Env.guard_f);
           FStar_TypeChecker_Env.deferred =
             (uu___278_1716.FStar_TypeChecker_Env.deferred);
           FStar_TypeChecker_Env.univ_ineqs =
             (uu___278_1716.FStar_TypeChecker_Env.univ_ineqs);
           FStar_TypeChecker_Env.implicits = imps
         }  in
       let g1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g
          in
       let ps' =
         let uu___282_1719 = ps  in
         {
           FStar_Tactics_Types.main_context =
             (uu___282_1719.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___282_1719.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (g1.FStar_TypeChecker_Env.implicits);
           FStar_Tactics_Types.goals =
             (uu___282_1719.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___282_1719.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___282_1719.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___282_1719.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___282_1719.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___282_1719.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___282_1719.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___282_1719.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___282_1719.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___282_1719.FStar_Tactics_Types.local_state)
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
          (fun uu____1746  ->
             (let uu____1748 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____1748
              then
                (FStar_Options.push ();
                 (let uu____1753 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____1757 = __do_unify env t1 t2  in
              bind uu____1757
                (fun r  ->
                   (let uu____1768 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1768 then FStar_Options.pop () else ());
                   ret r)))
  
let (remove_solved_goals : unit tac) =
  bind get
    (fun ps  ->
       let ps' =
         let uu___297_1782 = ps  in
         let uu____1783 =
           FStar_List.filter
             (fun g  ->
                let uu____1789 = check_goal_solved g  in
                FStar_Option.isNone uu____1789) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___297_1782.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___297_1782.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___297_1782.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1783;
           FStar_Tactics_Types.smt_goals =
             (uu___297_1782.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___297_1782.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___297_1782.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___297_1782.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___297_1782.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___297_1782.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___297_1782.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___297_1782.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___297_1782.FStar_Tactics_Types.local_state)
         }  in
       set ps')
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1807 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____1807 with
      | FStar_Pervasives_Native.Some uu____1812 ->
          let uu____1813 =
            let uu____1815 = goal_to_string_verbose goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____1815  in
          fail uu____1813
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____1836 = FStar_Tactics_Types.goal_env goal  in
      let uu____1837 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____1836 solution uu____1837
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____1844 =
         let uu___310_1845 = p  in
         let uu____1846 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___310_1845.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___310_1845.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___310_1845.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1846;
           FStar_Tactics_Types.smt_goals =
             (uu___310_1845.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___310_1845.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___310_1845.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___310_1845.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___310_1845.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___310_1845.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___310_1845.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___310_1845.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___310_1845.FStar_Tactics_Types.local_state)
         }  in
       set uu____1844)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      mlog
        (fun uu____1868  ->
           let uu____1869 =
             let uu____1871 = FStar_Tactics_Types.goal_witness goal  in
             FStar_Syntax_Print.term_to_string uu____1871  in
           let uu____1872 = FStar_Syntax_Print.term_to_string solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____1869 uu____1872)
        (fun uu____1877  ->
           let uu____1878 = trysolve goal solution  in
           bind uu____1878
             (fun b  ->
                if b
                then bind __dismiss (fun uu____1890  -> remove_solved_goals)
                else
                  (let uu____1893 =
                     let uu____1895 =
                       let uu____1897 = FStar_Tactics_Types.goal_env goal  in
                       tts uu____1897 solution  in
                     let uu____1898 =
                       let uu____1900 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1901 = FStar_Tactics_Types.goal_witness goal
                          in
                       tts uu____1900 uu____1901  in
                     let uu____1902 =
                       let uu____1904 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1905 = FStar_Tactics_Types.goal_type goal
                          in
                       tts uu____1904 uu____1905  in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____1895 uu____1898 uu____1902
                      in
                   fail uu____1893)))
  
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1922 = set_solution goal solution  in
      bind uu____1922
        (fun uu____1926  ->
           bind __dismiss (fun uu____1928  -> remove_solved_goals))
  
let (set_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___326_1947 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___326_1947.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___326_1947.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___326_1947.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals = gs;
              FStar_Tactics_Types.smt_goals =
                (uu___326_1947.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___326_1947.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___326_1947.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___326_1947.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___326_1947.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___326_1947.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___326_1947.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___326_1947.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___326_1947.FStar_Tactics_Types.local_state)
            }))
  
let (set_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___330_1966 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___330_1966.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___330_1966.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___330_1966.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___330_1966.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals = gs;
              FStar_Tactics_Types.depth =
                (uu___330_1966.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___330_1966.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___330_1966.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___330_1966.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___330_1966.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___330_1966.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___330_1966.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___330_1966.FStar_Tactics_Types.local_state)
            }))
  
let (dismiss_all : unit tac) = set_goals [] 
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____1982 = FStar_Options.defensive ()  in
    if uu____1982
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____1992 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____1992)
         in
      let b2 =
        b1 &&
          (let uu____1996 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____1996)
         in
      let rec aux b3 e =
        let uu____2011 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____2011 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____2031 =
        (let uu____2035 = aux b2 env  in Prims.op_Negation uu____2035) &&
          (let uu____2038 = FStar_ST.op_Bang nwarn  in
           uu____2038 < (Prims.parse_int "5"))
         in
      (if uu____2031
       then
         ((let uu____2064 =
             let uu____2065 = FStar_Tactics_Types.goal_type g  in
             uu____2065.FStar_Syntax_Syntax.pos  in
           let uu____2068 =
             let uu____2074 =
               let uu____2076 = goal_to_string_verbose g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____2076
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____2074)  in
           FStar_Errors.log_issue uu____2064 uu____2068);
          (let uu____2080 =
             let uu____2082 = FStar_ST.op_Bang nwarn  in
             uu____2082 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____2080))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___352_2151 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___352_2151.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___352_2151.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___352_2151.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___352_2151.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___352_2151.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___352_2151.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___352_2151.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___352_2151.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___352_2151.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___352_2151.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___352_2151.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___352_2151.FStar_Tactics_Types.local_state)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___357_2172 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___357_2172.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___357_2172.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___357_2172.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___357_2172.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___357_2172.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___357_2172.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___357_2172.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___357_2172.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___357_2172.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___357_2172.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___357_2172.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___357_2172.FStar_Tactics_Types.local_state)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___362_2193 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___362_2193.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___362_2193.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___362_2193.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___362_2193.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___362_2193.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___362_2193.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___362_2193.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___362_2193.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___362_2193.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___362_2193.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___362_2193.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___362_2193.FStar_Tactics_Types.local_state)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___367_2214 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___367_2214.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___367_2214.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___367_2214.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___367_2214.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___367_2214.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___367_2214.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___367_2214.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___367_2214.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___367_2214.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___367_2214.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___367_2214.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___367_2214.FStar_Tactics_Types.local_state)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____2226  -> add_goals [g]) 
let (new_uvar :
  Prims.string ->
    env ->
      FStar_Reflection_Data.typ ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar) tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____2257 =
          FStar_TypeChecker_Env.new_implicit_var_aux reason
            typ.FStar_Syntax_Syntax.pos env typ
            FStar_Syntax_Syntax.Allow_untyped FStar_Pervasives_Native.None
           in
        match uu____2257 with
        | (u,ctx_uvar,g_u) ->
            let uu____2295 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____2295
              (fun uu____2304  ->
                 let uu____2305 =
                   let uu____2310 =
                     let uu____2311 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____2311  in
                   (u, uu____2310)  in
                 ret uu____2305)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2332 = FStar_Syntax_Util.un_squash t1  in
    match uu____2332 with
    | FStar_Pervasives_Native.Some t' ->
        let t'1 = FStar_Syntax_Util.unascribe t'  in
        let uu____2344 =
          let uu____2345 = FStar_Syntax_Subst.compress t'1  in
          uu____2345.FStar_Syntax_Syntax.n  in
        (match uu____2344 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____2350 -> false)
    | uu____2352 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2365 = FStar_Syntax_Util.un_squash t  in
    match uu____2365 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____2376 =
          let uu____2377 = FStar_Syntax_Subst.compress t'  in
          uu____2377.FStar_Syntax_Syntax.n  in
        (match uu____2376 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____2382 -> false)
    | uu____2384 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____2397  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____2409 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____2409 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____2416 = goal_to_string_verbose hd1  in
                    let uu____2418 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____2416 uu____2418);
                   ret hd1)))
  
let (tadmit_t : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____2431 =
      bind get
        (fun ps  ->
           let uu____2437 = cur_goal ()  in
           bind uu____2437
             (fun g  ->
                (let uu____2444 =
                   let uu____2445 = FStar_Tactics_Types.goal_type g  in
                   uu____2445.FStar_Syntax_Syntax.pos  in
                 let uu____2448 =
                   let uu____2454 =
                     let uu____2456 =
                       goal_to_string "" FStar_Pervasives_Native.None ps g
                        in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____2456
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____2454)  in
                 FStar_Errors.log_issue uu____2444 uu____2448);
                solve' g t))
       in
    FStar_All.pipe_left (wrap_err "tadmit_t") uu____2431
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____2479  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___412_2490 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___412_2490.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___412_2490.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___412_2490.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___412_2490.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___412_2490.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___412_2490.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___412_2490.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___412_2490.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___412_2490.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___412_2490.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___412_2490.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (uu___412_2490.FStar_Tactics_Types.local_state)
           }  in
         let uu____2492 = set ps1  in
         bind uu____2492
           (fun uu____2497  ->
              let uu____2498 = FStar_BigInt.of_int_fs n1  in ret uu____2498))
  
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
              let uu____2536 = env.FStar_TypeChecker_Env.universe_of env phi
                 in
              FStar_Syntax_Util.mk_squash uu____2536 phi  in
            let uu____2537 = new_uvar reason env typ  in
            bind uu____2537
              (fun uu____2552  ->
                 match uu____2552 with
                 | (uu____2559,ctx_uvar) ->
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
             (fun uu____2606  ->
                let uu____2607 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2607)
             (fun uu____2612  ->
                let e1 =
                  let uu___430_2614 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___430_2614.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___430_2614.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___430_2614.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___430_2614.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___430_2614.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___430_2614.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___430_2614.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___430_2614.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___430_2614.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___430_2614.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___430_2614.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___430_2614.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___430_2614.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___430_2614.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___430_2614.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___430_2614.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___430_2614.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___430_2614.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___430_2614.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___430_2614.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___430_2614.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___430_2614.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___430_2614.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___430_2614.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___430_2614.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___430_2614.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___430_2614.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___430_2614.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___430_2614.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___430_2614.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___430_2614.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___430_2614.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___430_2614.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___430_2614.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___430_2614.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___430_2614.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___430_2614.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___430_2614.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___430_2614.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___430_2614.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___430_2614.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___430_2614.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___434_2626  ->
                     match () with
                     | () ->
                         let uu____2635 =
                           FStar_TypeChecker_TcTerm.type_of_tot_term e1 t  in
                         ret uu____2635) ()
                with
                | FStar_Errors.Err (uu____2662,msg) ->
                    let uu____2666 = tts e1 t  in
                    let uu____2668 =
                      let uu____2670 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2670
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2666 uu____2668 msg
                | FStar_Errors.Error (uu____2680,msg,uu____2682) ->
                    let uu____2685 = tts e1 t  in
                    let uu____2687 =
                      let uu____2689 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2689
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2685 uu____2687 msg))
  
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
             (fun uu____2742  ->
                let uu____2743 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc_ghost(%s)\n" uu____2743)
             (fun uu____2748  ->
                let e1 =
                  let uu___451_2750 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___451_2750.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___451_2750.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___451_2750.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___451_2750.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___451_2750.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___451_2750.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___451_2750.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___451_2750.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___451_2750.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___451_2750.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___451_2750.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___451_2750.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___451_2750.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___451_2750.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___451_2750.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___451_2750.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___451_2750.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___451_2750.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___451_2750.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___451_2750.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___451_2750.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___451_2750.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___451_2750.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___451_2750.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___451_2750.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___451_2750.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___451_2750.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___451_2750.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___451_2750.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___451_2750.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___451_2750.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___451_2750.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___451_2750.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___451_2750.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___451_2750.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___451_2750.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___451_2750.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___451_2750.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___451_2750.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___451_2750.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___451_2750.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___451_2750.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___455_2765  ->
                     match () with
                     | () ->
                         let uu____2774 =
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e1 t
                            in
                         (match uu____2774 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____2812,msg) ->
                    let uu____2816 = tts e1 t  in
                    let uu____2818 =
                      let uu____2820 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2820
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2816 uu____2818 msg
                | FStar_Errors.Error (uu____2830,msg,uu____2832) ->
                    let uu____2835 = tts e1 t  in
                    let uu____2837 =
                      let uu____2839 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2839
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2835 uu____2837 msg))
  
let (__tc_lax :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
        FStar_TypeChecker_Env.guard_t) tac)
  =
  fun e  ->
    fun t  ->
      bind get
        (fun ps  ->
           mlog
             (fun uu____2892  ->
                let uu____2893 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2893)
             (fun uu____2899  ->
                let e1 =
                  let uu___476_2901 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___476_2901.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___476_2901.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___476_2901.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___476_2901.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___476_2901.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___476_2901.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___476_2901.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___476_2901.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___476_2901.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___476_2901.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___476_2901.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___476_2901.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___476_2901.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___476_2901.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___476_2901.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___476_2901.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___476_2901.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___476_2901.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___476_2901.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___476_2901.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___476_2901.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___476_2901.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___476_2901.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___476_2901.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___476_2901.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___476_2901.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___476_2901.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___476_2901.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___476_2901.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___476_2901.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___476_2901.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___476_2901.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___476_2901.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___476_2901.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___476_2901.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___476_2901.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___476_2901.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___476_2901.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___476_2901.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___476_2901.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___476_2901.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___476_2901.FStar_TypeChecker_Env.nbe)
                  }  in
                let e2 =
                  let uu___479_2904 = e1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___479_2904.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___479_2904.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___479_2904.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___479_2904.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___479_2904.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___479_2904.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___479_2904.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___479_2904.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___479_2904.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___479_2904.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___479_2904.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___479_2904.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___479_2904.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___479_2904.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___479_2904.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___479_2904.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___479_2904.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___479_2904.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___479_2904.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___479_2904.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___479_2904.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___479_2904.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___479_2904.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___479_2904.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___479_2904.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___479_2904.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___479_2904.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___479_2904.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___479_2904.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___479_2904.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___479_2904.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___479_2904.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___479_2904.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___479_2904.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___479_2904.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___479_2904.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___479_2904.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___479_2904.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___479_2904.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___479_2904.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___479_2904.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___479_2904.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___483_2916  ->
                     match () with
                     | () ->
                         let uu____2925 =
                           FStar_TypeChecker_TcTerm.tc_term e2 t  in
                         ret uu____2925) ()
                with
                | FStar_Errors.Err (uu____2952,msg) ->
                    let uu____2956 = tts e2 t  in
                    let uu____2958 =
                      let uu____2960 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____2960
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2956 uu____2958 msg
                | FStar_Errors.Error (uu____2970,msg,uu____2972) ->
                    let uu____2975 = tts e2 t  in
                    let uu____2977 =
                      let uu____2979 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____2979
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2975 uu____2977 msg))
  
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
  fun uu____3013  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___504_3032 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___504_3032.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___504_3032.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___504_3032.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___504_3032.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___504_3032.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___504_3032.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___504_3032.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___504_3032.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___504_3032.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___504_3032.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___504_3032.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___504_3032.FStar_Tactics_Types.local_state)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____3057 = get_guard_policy ()  in
      bind uu____3057
        (fun old_pol  ->
           let uu____3063 = set_guard_policy pol  in
           bind uu____3063
             (fun uu____3067  ->
                bind t
                  (fun r  ->
                     let uu____3071 = set_guard_policy old_pol  in
                     bind uu____3071 (fun uu____3075  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____3079 = let uu____3084 = cur_goal ()  in trytac uu____3084  in
  bind uu____3079
    (fun uu___0_3091  ->
       match uu___0_3091 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____3097 = FStar_Options.peek ()  in ret uu____3097)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        mlog
          (fun uu____3122  ->
             let uu____3123 = FStar_TypeChecker_Rel.guard_to_string e g  in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason uu____3123)
          (fun uu____3128  ->
             let uu____3129 = add_implicits g.FStar_TypeChecker_Env.implicits
                in
             bind uu____3129
               (fun uu____3133  ->
                  bind getopts
                    (fun opts  ->
                       let uu____3137 =
                         let uu____3138 =
                           FStar_TypeChecker_Rel.simplify_guard e g  in
                         uu____3138.FStar_TypeChecker_Env.guard_f  in
                       match uu____3137 with
                       | FStar_TypeChecker_Common.Trivial  -> ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____3142 = istrivial e f  in
                           if uu____3142
                           then ret ()
                           else
                             bind get
                               (fun ps  ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop  ->
                                      ((let uu____3155 =
                                          let uu____3161 =
                                            let uu____3163 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g
                                               in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____3163
                                             in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____3161)
                                           in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____3155);
                                       ret ())
                                  | FStar_Tactics_Types.Goal  ->
                                      mlog
                                        (fun uu____3169  ->
                                           let uu____3170 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____3170)
                                        (fun uu____3175  ->
                                           let uu____3176 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____3176
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___533_3184 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___533_3184.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___533_3184.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___533_3184.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___533_3184.FStar_Tactics_Types.label)
                                                  }  in
                                                push_goals [goal1]))
                                  | FStar_Tactics_Types.SMT  ->
                                      mlog
                                        (fun uu____3188  ->
                                           let uu____3189 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____3189)
                                        (fun uu____3194  ->
                                           let uu____3195 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____3195
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___540_3203 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___540_3203.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___540_3203.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___540_3203.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___540_3203.FStar_Tactics_Types.label)
                                                  }  in
                                                push_smt_goals [goal1]))
                                  | FStar_Tactics_Types.Force  ->
                                      mlog
                                        (fun uu____3207  ->
                                           let uu____3208 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____3208)
                                        (fun uu____3212  ->
                                           try
                                             (fun uu___547_3217  ->
                                                match () with
                                                | () ->
                                                    let uu____3220 =
                                                      let uu____3222 =
                                                        let uu____3224 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____3224
                                                         in
                                                      Prims.op_Negation
                                                        uu____3222
                                                       in
                                                    if uu____3220
                                                    then
                                                      mlog
                                                        (fun uu____3231  ->
                                                           let uu____3232 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g
                                                              in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____3232)
                                                        (fun uu____3236  ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else ret ()) ()
                                           with
                                           | uu___546_3241 ->
                                               mlog
                                                 (fun uu____3246  ->
                                                    let uu____3247 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g
                                                       in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____3247)
                                                 (fun uu____3251  ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
  
let (tcc : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp tac) =
  fun t  ->
    let uu____3263 =
      let uu____3266 = cur_goal ()  in
      bind uu____3266
        (fun goal  ->
           let uu____3272 =
             let uu____3281 = FStar_Tactics_Types.goal_env goal  in
             __tc_lax uu____3281 t  in
           bind uu____3272
             (fun uu____3293  ->
                match uu____3293 with
                | (uu____3302,lc,uu____3304) ->
                    let uu____3305 = FStar_Syntax_Syntax.lcomp_comp lc  in
                    ret uu____3305))
       in
    FStar_All.pipe_left (wrap_err "tcc") uu____3263
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____3321 =
      let uu____3326 = tcc t  in
      bind uu____3326 (fun c  -> ret (FStar_Syntax_Util.comp_result c))  in
    FStar_All.pipe_left (wrap_err "tc") uu____3321
  
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
            let uu____3378 = mk_irrelevant_goal reason env phi opts label1
               in
            bind uu____3378 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____3390  ->
    let uu____3393 = cur_goal ()  in
    bind uu____3393
      (fun goal  ->
         let uu____3399 =
           let uu____3401 = FStar_Tactics_Types.goal_env goal  in
           let uu____3402 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____3401 uu____3402  in
         if uu____3399
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____3408 =
              let uu____3410 = FStar_Tactics_Types.goal_env goal  in
              let uu____3411 = FStar_Tactics_Types.goal_type goal  in
              tts uu____3410 uu____3411  in
            fail1 "Not a trivial goal: %s" uu____3408))
  
let divide : 'a 'b . FStar_BigInt.t -> 'a tac -> 'b tac -> ('a * 'b) tac =
  fun n1  ->
    fun l  ->
      fun r  ->
        bind get
          (fun p  ->
             let uu____3462 =
               try
                 (fun uu___605_3485  ->
                    match () with
                    | () ->
                        let uu____3496 =
                          let uu____3505 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____3505
                            p.FStar_Tactics_Types.goals
                           in
                        ret uu____3496) ()
               with | uu___604_3516 -> fail "divide: not enough goals"  in
             bind uu____3462
               (fun uu____3553  ->
                  match uu____3553 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___587_3579 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___587_3579.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___587_3579.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___587_3579.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___587_3579.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___587_3579.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___587_3579.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___587_3579.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___587_3579.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___587_3579.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___587_3579.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___587_3579.FStar_Tactics_Types.local_state)
                        }  in
                      let uu____3580 = set lp  in
                      bind uu____3580
                        (fun uu____3588  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___593_3604 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___593_3604.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___593_3604.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___593_3604.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___593_3604.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___593_3604.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___593_3604.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___593_3604.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___593_3604.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___593_3604.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___593_3604.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___593_3604.FStar_Tactics_Types.local_state)
                                       }  in
                                     let uu____3605 = set rp  in
                                     bind uu____3605
                                       (fun uu____3613  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___599_3629 = rp'
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___599_3629.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___599_3629.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___599_3629.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___599_3629.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___599_3629.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___599_3629.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___599_3629.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___599_3629.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___599_3629.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___599_3629.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___599_3629.FStar_Tactics_Types.local_state)
                                                      }  in
                                                    let uu____3630 = set p'
                                                       in
                                                    bind uu____3630
                                                      (fun uu____3638  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____3644 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____3666 = divide FStar_BigInt.one f idtac  in
    bind uu____3666
      (fun uu____3679  -> match uu____3679 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____3717::uu____3718 ->
             let uu____3721 =
               let uu____3730 = map tau  in
               divide FStar_BigInt.one tau uu____3730  in
             bind uu____3721
               (fun uu____3748  ->
                  match uu____3748 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____3790 =
        bind t1
          (fun uu____3795  ->
             let uu____3796 = map t2  in
             bind uu____3796 (fun uu____3804  -> ret ()))
         in
      focus uu____3790
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____3814  ->
    let uu____3817 =
      let uu____3820 = cur_goal ()  in
      bind uu____3820
        (fun goal  ->
           let uu____3829 =
             let uu____3836 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____3836  in
           match uu____3829 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____3845 =
                 let uu____3847 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____3847  in
               if uu____3845
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____3856 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____3856 [b]  in
                  let typ' = FStar_Syntax_Util.comp_result c  in
                  let uu____3872 = new_uvar "intro" env' typ'  in
                  bind uu____3872
                    (fun uu____3889  ->
                       match uu____3889 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c))
                              in
                           let uu____3913 = set_solution goal sol  in
                           bind uu____3913
                             (fun uu____3919  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                    goal.FStar_Tactics_Types.label
                                   in
                                let uu____3921 =
                                  let uu____3924 = bnorm_goal g  in
                                  replace_cur uu____3924  in
                                bind uu____3921 (fun uu____3926  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____3931 =
                 let uu____3933 = FStar_Tactics_Types.goal_env goal  in
                 let uu____3934 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____3933 uu____3934  in
               fail1 "goal is not an arrow (%s)" uu____3931)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____3817
  
let (intro_rec :
  unit -> (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder) tac) =
  fun uu____3952  ->
    let uu____3959 = cur_goal ()  in
    bind uu____3959
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____3978 =
            let uu____3985 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____3985  in
          match uu____3978 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____3998 =
                let uu____4000 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____4000  in
              if uu____3998
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____4017 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____4017
                    in
                 let bs =
                   let uu____4028 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____4028; b]  in
                 let env' =
                   let uu____4054 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____4054 bs  in
                 let uu____4055 =
                   new_uvar "intro_rec" env'
                     (FStar_Syntax_Util.comp_result c)
                    in
                 bind uu____4055
                   (fun uu____4081  ->
                      match uu____4081 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____4095 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____4098 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____4095
                              FStar_Parser_Const.effect_Tot_lid uu____4098 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____4116 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____4116 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____4138 =
                                   let uu____4139 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____4139.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____4138
                                  in
                               let uu____4155 = set_solution goal tm  in
                               bind uu____4155
                                 (fun uu____4164  ->
                                    let uu____4165 =
                                      let uu____4168 =
                                        bnorm_goal
                                          (let uu___670_4171 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___670_4171.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___670_4171.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___670_4171.FStar_Tactics_Types.is_guard);
                                             FStar_Tactics_Types.label =
                                               (uu___670_4171.FStar_Tactics_Types.label)
                                           })
                                         in
                                      replace_cur uu____4168  in
                                    bind uu____4165
                                      (fun uu____4178  ->
                                         let uu____4179 =
                                           let uu____4184 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____4184, b)  in
                                         ret uu____4179)))))
          | FStar_Pervasives_Native.None  ->
              let uu____4193 =
                let uu____4195 = FStar_Tactics_Types.goal_env goal  in
                let uu____4196 = FStar_Tactics_Types.goal_type goal  in
                tts uu____4195 uu____4196  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____4193))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____4216 = cur_goal ()  in
    bind uu____4216
      (fun goal  ->
         mlog
           (fun uu____4223  ->
              let uu____4224 =
                let uu____4226 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____4226  in
              FStar_Util.print1 "norm: witness = %s\n" uu____4224)
           (fun uu____4232  ->
              let steps =
                let uu____4236 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____4236
                 in
              let t =
                let uu____4240 = FStar_Tactics_Types.goal_env goal  in
                let uu____4241 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____4240 uu____4241  in
              let uu____4242 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____4242))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____4267 =
          bind get
            (fun ps  ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
                 | g::uu____4275 -> g.FStar_Tactics_Types.opts
                 | uu____4278 -> FStar_Options.peek ()  in
               mlog
                 (fun uu____4283  ->
                    let uu____4284 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____4284)
                 (fun uu____4289  ->
                    let uu____4290 = __tc_lax e t  in
                    bind uu____4290
                      (fun uu____4311  ->
                         match uu____4311 with
                         | (t1,uu____4321,uu____4322) ->
                             let steps =
                               let uu____4326 =
                                 FStar_TypeChecker_Normalize.tr_norm_steps s
                                  in
                               FStar_List.append
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu____4326
                                in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1
                                in
                             mlog
                               (fun uu____4332  ->
                                  let uu____4333 =
                                    FStar_Syntax_Print.term_to_string t2  in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____4333)
                               (fun uu____4337  -> ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____4267
  
let (refine_intro : unit -> unit tac) =
  fun uu____4350  ->
    let uu____4353 =
      let uu____4356 = cur_goal ()  in
      bind uu____4356
        (fun g  ->
           let uu____4363 =
             let uu____4374 = FStar_Tactics_Types.goal_env g  in
             let uu____4375 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____4374 uu____4375
              in
           match uu____4363 with
           | (uu____4378,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____4404 =
                 let uu____4409 =
                   let uu____4414 =
                     let uu____4415 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____4415]  in
                   FStar_Syntax_Subst.open_term uu____4414 phi  in
                 match uu____4409 with
                 | (bvs,phi1) ->
                     let uu____4440 =
                       let uu____4441 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____4441  in
                     (uu____4440, phi1)
                  in
               (match uu____4404 with
                | (bv1,phi1) ->
                    let uu____4460 =
                      let uu____4463 = FStar_Tactics_Types.goal_env g  in
                      let uu____4464 =
                        let uu____4465 =
                          let uu____4468 =
                            let uu____4469 =
                              let uu____4476 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____4476)  in
                            FStar_Syntax_Syntax.NT uu____4469  in
                          [uu____4468]  in
                        FStar_Syntax_Subst.subst uu____4465 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____4463
                        uu____4464 g.FStar_Tactics_Types.opts
                        g.FStar_Tactics_Types.label
                       in
                    bind uu____4460
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____4485  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____4353
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____4508 = cur_goal ()  in
      bind uu____4508
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____4517 = FStar_Tactics_Types.goal_env goal  in
               let uu____4518 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____4517 uu____4518
             else FStar_Tactics_Types.goal_env goal  in
           let uu____4521 = __tc env t  in
           bind uu____4521
             (fun uu____4540  ->
                match uu____4540 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____4555  ->
                         let uu____4556 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____4558 =
                           let uu____4560 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____4560
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____4556 uu____4558)
                      (fun uu____4564  ->
                         let uu____4565 =
                           let uu____4568 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____4568 guard  in
                         bind uu____4565
                           (fun uu____4571  ->
                              mlog
                                (fun uu____4575  ->
                                   let uu____4576 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____4578 =
                                     let uu____4580 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____4580
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____4576 uu____4578)
                                (fun uu____4584  ->
                                   let uu____4585 =
                                     let uu____4589 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____4590 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____4589 typ uu____4590  in
                                   bind uu____4585
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____4600 =
                                             let uu____4602 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____4602 t1  in
                                           let uu____4603 =
                                             let uu____4605 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____4605 typ  in
                                           let uu____4606 =
                                             let uu____4608 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____4609 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____4608 uu____4609  in
                                           let uu____4610 =
                                             let uu____4612 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____4613 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____4612 uu____4613  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____4600 uu____4603 uu____4606
                                             uu____4610)))))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun try_refine  ->
    fun set_expected_typ1  ->
      fun tm  ->
        let uu____4639 =
          mlog
            (fun uu____4644  ->
               let uu____4645 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____4645)
            (fun uu____4650  ->
               let uu____4651 =
                 let uu____4658 = __exact_now set_expected_typ1 tm  in
                 catch uu____4658  in
               bind uu____4651
                 (fun uu___2_4667  ->
                    match uu___2_4667 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        traise e
                    | FStar_Util.Inl e ->
                        mlog
                          (fun uu____4678  ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____4682  ->
                             let uu____4683 =
                               let uu____4690 =
                                 let uu____4693 =
                                   norm [FStar_Syntax_Embeddings.Delta]  in
                                 bind uu____4693
                                   (fun uu____4698  ->
                                      let uu____4699 = refine_intro ()  in
                                      bind uu____4699
                                        (fun uu____4703  ->
                                           __exact_now set_expected_typ1 tm))
                                  in
                               catch uu____4690  in
                             bind uu____4683
                               (fun uu___1_4710  ->
                                  match uu___1_4710 with
                                  | FStar_Util.Inr r ->
                                      mlog
                                        (fun uu____4719  ->
                                           FStar_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu____4722  -> ret ())
                                  | FStar_Util.Inl uu____4723 ->
                                      mlog
                                        (fun uu____4725  ->
                                           FStar_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu____4728  -> traise e)))))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____4639
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____4780 = f x  in
          bind uu____4780
            (fun y  ->
               let uu____4788 = mapM f xs  in
               bind uu____4788 (fun ys  -> ret (y :: ys)))
  
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
          let uu____4860 = do_unify e ty1 ty2  in
          bind uu____4860
            (fun uu___3_4874  ->
               if uu___3_4874
               then ret acc
               else
                 (let uu____4894 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____4894 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____4915 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____4917 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____4915
                        uu____4917
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____4934 =
                        let uu____4936 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____4936  in
                      if uu____4934
                      then fail "Codomain is effectful"
                      else
                        (let uu____4960 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____4960
                           (fun uu____4987  ->
                              match uu____4987 with
                              | (uvt,uv) ->
                                  let typ = FStar_Syntax_Util.comp_result c
                                     in
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
      let uu____5079 =
        mlog
          (fun uu____5084  ->
             let uu____5085 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_apply: tm = %s\n" uu____5085)
          (fun uu____5090  ->
             let uu____5091 = cur_goal ()  in
             bind uu____5091
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____5099 = __tc e tm  in
                  bind uu____5099
                    (fun uu____5120  ->
                       match uu____5120 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____5133 =
                             let uu____5144 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____5144  in
                           bind uu____5133
                             (fun uvs  ->
                                let fix_qual q =
                                  match q with
                                  | FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Meta uu____5182)
                                      ->
                                      FStar_Pervasives_Native.Some
                                        (FStar_Syntax_Syntax.Implicit false)
                                  | uu____5186 -> q  in
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____5209  ->
                                       fun w  ->
                                         match uu____5209 with
                                         | (uvt,q,uu____5227) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, (fix_qual q))]) uvs tm1
                                   in
                                let uvset =
                                  let uu____5259 =
                                    FStar_Syntax_Free.new_uv_set ()  in
                                  FStar_List.fold_right
                                    (fun uu____5276  ->
                                       fun s  ->
                                         match uu____5276 with
                                         | (uu____5288,uu____5289,uv) ->
                                             let uu____5291 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                in
                                             FStar_Util.set_union s
                                               uu____5291) uvs uu____5259
                                   in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset  in
                                let uu____5301 = solve' goal w  in
                                bind uu____5301
                                  (fun uu____5306  ->
                                     let uu____5307 =
                                       mapM
                                         (fun uu____5324  ->
                                            match uu____5324 with
                                            | (uvt,q,uv) ->
                                                let uu____5336 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                   in
                                                (match uu____5336 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____5341 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____5342 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv)
                                                        in
                                                     if uu____5342
                                                     then ret ()
                                                     else
                                                       (let uu____5349 =
                                                          let uu____5352 =
                                                            bnorm_goal
                                                              (let uu___831_5355
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___831_5355.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___831_5355.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false;
                                                                 FStar_Tactics_Types.label
                                                                   =
                                                                   (uu___831_5355.FStar_Tactics_Types.label)
                                                               })
                                                             in
                                                          [uu____5352]  in
                                                        add_goals uu____5349)))
                                         uvs
                                        in
                                     bind uu____5307
                                       (fun uu____5360  ->
                                          proc_guard "apply guard" e guard))))))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____5079
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____5388 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____5388
    then
      let uu____5397 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____5412 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____5465 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____5397 with
      | (pre,post) ->
          let post1 =
            let uu____5498 =
              let uu____5509 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____5509]  in
            FStar_Syntax_Util.mk_app post uu____5498  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____5540 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____5540
       then
         let uu____5549 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____5549
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
            let uu____5628 = f x e  in
            bind uu____5628 (fun e'  -> fold_left f e' xs1)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____5643 =
      let uu____5646 =
        bind get
          (fun ps  ->
             mlog
               (fun uu____5653  ->
                  let uu____5654 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____5654)
               (fun uu____5660  ->
                  let is_unit_t t =
                    let uu____5668 =
                      let uu____5669 = FStar_Syntax_Subst.compress t  in
                      uu____5669.FStar_Syntax_Syntax.n  in
                    match uu____5668 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____5675 -> false  in
                  let uu____5677 = cur_goal ()  in
                  bind uu____5677
                    (fun goal  ->
                       let uu____5683 =
                         let uu____5692 = FStar_Tactics_Types.goal_env goal
                            in
                         __tc uu____5692 tm  in
                       bind uu____5683
                         (fun uu____5707  ->
                            match uu____5707 with
                            | (tm1,t,guard) ->
                                let uu____5719 =
                                  FStar_Syntax_Util.arrow_formals_comp t  in
                                (match uu____5719 with
                                 | (bs,comp) ->
                                     let uu____5752 = lemma_or_sq comp  in
                                     (match uu____5752 with
                                      | FStar_Pervasives_Native.None  ->
                                          fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre,post) ->
                                          let uu____5772 =
                                            fold_left
                                              (fun uu____5834  ->
                                                 fun uu____5835  ->
                                                   match (uu____5834,
                                                           uu____5835)
                                                   with
                                                   | ((b,aq),(uvs,imps,subst1))
                                                       ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst1
                                                           b.FStar_Syntax_Syntax.sort
                                                          in
                                                       let uu____5986 =
                                                         is_unit_t b_t  in
                                                       if uu____5986
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
                                                         (let uu____6109 =
                                                            let uu____6116 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            new_uvar
                                                              "apply_lemma"
                                                              uu____6116 b_t
                                                             in
                                                          bind uu____6109
                                                            (fun uu____6147 
                                                               ->
                                                               match uu____6147
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
                                          bind uu____5772
                                            (fun uu____6333  ->
                                               match uu____6333 with
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
                                                   let uu____6421 =
                                                     let uu____6425 =
                                                       FStar_Tactics_Types.goal_env
                                                         goal
                                                        in
                                                     let uu____6426 =
                                                       FStar_Syntax_Util.mk_squash
                                                         FStar_Syntax_Syntax.U_zero
                                                         post1
                                                        in
                                                     let uu____6427 =
                                                       FStar_Tactics_Types.goal_type
                                                         goal
                                                        in
                                                     do_unify uu____6425
                                                       uu____6426 uu____6427
                                                      in
                                                   bind uu____6421
                                                     (fun b  ->
                                                        if
                                                          Prims.op_Negation b
                                                        then
                                                          let uu____6438 =
                                                            let uu____6440 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            tts uu____6440
                                                              tm1
                                                             in
                                                          let uu____6441 =
                                                            let uu____6443 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            let uu____6444 =
                                                              FStar_Syntax_Util.mk_squash
                                                                FStar_Syntax_Syntax.U_zero
                                                                post1
                                                               in
                                                            tts uu____6443
                                                              uu____6444
                                                             in
                                                          let uu____6445 =
                                                            let uu____6447 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            let uu____6448 =
                                                              FStar_Tactics_Types.goal_type
                                                                goal
                                                               in
                                                            tts uu____6447
                                                              uu____6448
                                                             in
                                                          fail3
                                                            "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                            uu____6438
                                                            uu____6441
                                                            uu____6445
                                                        else
                                                          (let uu____6452 =
                                                             solve' goal
                                                               FStar_Syntax_Util.exp_unit
                                                              in
                                                           bind uu____6452
                                                             (fun uu____6460 
                                                                ->
                                                                let is_free_uvar
                                                                  uv t1 =
                                                                  let free_uvars
                                                                    =
                                                                    let uu____6486
                                                                    =
                                                                    let uu____6489
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____6489
                                                                     in
                                                                    FStar_List.map
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____6486
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
                                                                    let uu____6525
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____6525)
                                                                    goals
                                                                   in
                                                                let checkone
                                                                  t1 goals =
                                                                  let uu____6542
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                  match uu____6542
                                                                  with
                                                                  | (hd1,uu____6561)
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____6588)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____6605
                                                                    -> false)
                                                                   in
                                                                let uu____6607
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
                                                                    let uu____6650
                                                                    = imp  in
                                                                    match uu____6650
                                                                    with
                                                                    | 
                                                                    (term,ctx_uvar)
                                                                    ->
                                                                    let uu____6661
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____6661
                                                                    with
                                                                    | 
                                                                    (hd1,uu____6683)
                                                                    ->
                                                                    let uu____6708
                                                                    =
                                                                    let uu____6709
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____6709.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____6708
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____6717)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___941_6737
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___941_6737.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___941_6737.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___941_6737.FStar_Tactics_Types.is_guard);
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___941_6737.FStar_Tactics_Types.label)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____6740
                                                                    ->
                                                                    mlog
                                                                    (fun
                                                                    uu____6746
                                                                     ->
                                                                    let uu____6747
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                                                     in
                                                                    let uu____6749
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____6747
                                                                    uu____6749)
                                                                    (fun
                                                                    uu____6756
                                                                     ->
                                                                    let env =
                                                                    let uu___946_6758
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___946_6758.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___946_6758.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___946_6758.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___946_6758.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___946_6758.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___946_6758.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___946_6758.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___946_6758.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___946_6758.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___946_6758.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___946_6758.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___946_6758.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___946_6758.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___946_6758.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___946_6758.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___946_6758.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___946_6758.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___946_6758.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___946_6758.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___946_6758.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___946_6758.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___946_6758.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___946_6758.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___946_6758.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___946_6758.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___946_6758.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___946_6758.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___946_6758.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___946_6758.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___946_6758.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___946_6758.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___946_6758.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___946_6758.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___946_6758.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___946_6758.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___946_6758.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___946_6758.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___946_6758.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___946_6758.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___946_6758.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___946_6758.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___946_6758.FStar_TypeChecker_Env.nbe)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let uu____6761
                                                                    =
                                                                    let uu____6764
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____6768
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
                                                                    let uu____6770
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____6768
                                                                    uu____6770
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____6776
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    uu____6764
                                                                    uu____6776
                                                                    g_typ  in
                                                                    bind
                                                                    uu____6761
                                                                    (fun
                                                                    uu____6780
                                                                     ->
                                                                    ret []))))))
                                                                   in
                                                                bind
                                                                  uu____6607
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
                                                                    let uu____6844
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____6844
                                                                    then
                                                                    let uu____6849
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____6849
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
                                                                    let uu____6864
                                                                    =
                                                                    let uu____6866
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____6866
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____6864)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____6867
                                                                    =
                                                                    let uu____6870
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____6870
                                                                    guard  in
                                                                    bind
                                                                    uu____6867
                                                                    (fun
                                                                    uu____6874
                                                                     ->
                                                                    let uu____6875
                                                                    =
                                                                    let uu____6878
                                                                    =
                                                                    let uu____6880
                                                                    =
                                                                    let uu____6882
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____6883
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____6882
                                                                    uu____6883
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____6880
                                                                     in
                                                                    if
                                                                    uu____6878
                                                                    then
                                                                    let uu____6887
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____6887
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    goal.FStar_Tactics_Types.label
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____6875
                                                                    (fun
                                                                    uu____6892
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2)))))))))))))
         in
      focus uu____5646  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____5643
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____6916 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____6916 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____6926::(e1,uu____6928)::(e2,uu____6930)::[])) when
        (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) ||
          (FStar_Ident.lid_equals l FStar_Parser_Const.c_eq2_lid)
        -> FStar_Pervasives_Native.Some (e1, e2)
    | uu____6991 ->
        let uu____6994 = FStar_Syntax_Util.unb2t typ  in
        (match uu____6994 with
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some t ->
             ((let uu____7009 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "GG t = %s\n" uu____7009);
              (let uu____7012 = FStar_Syntax_Util.head_and_args t  in
               match uu____7012 with
               | (hd1,args) ->
                   let uu____7061 =
                     let uu____7076 =
                       let uu____7077 = FStar_Syntax_Subst.compress hd1  in
                       uu____7077.FStar_Syntax_Syntax.n  in
                     (uu____7076, args)  in
                   (match uu____7061 with
                    | (FStar_Syntax_Syntax.Tm_fvar
                       fv,(uu____7097,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit uu____7098))::
                       (e1,FStar_Pervasives_Native.None )::(e2,FStar_Pervasives_Native.None
                                                            )::[])
                        when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.op_Eq
                        ->
                        ((let uu____7163 =
                            FStar_Syntax_Print.term_to_string e1  in
                          let uu____7165 =
                            FStar_Syntax_Print.term_to_string e2  in
                          FStar_Util.print2 "wat %s -- %s\n" uu____7163
                            uu____7165);
                         FStar_Pervasives_Native.Some (e1, e2))
                    | uu____7172 -> FStar_Pervasives_Native.None))))
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____7209 = destruct_eq' typ  in
    match uu____7209 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____7239 = FStar_Syntax_Util.un_squash typ  in
        (match uu____7239 with
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
        let uu____7308 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____7308 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', bv', [])
            else
              (let uu____7366 = aux e'  in
               FStar_Util.map_opt uu____7366
                 (fun uu____7397  ->
                    match uu____7397 with
                    | (e'',bv,bvs) -> (e'', bv, (bv' :: bvs))))
         in
      let uu____7423 = aux e  in
      FStar_Util.map_opt uu____7423
        (fun uu____7454  ->
           match uu____7454 with
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
          let uu____7528 =
            let uu____7539 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____7539  in
          FStar_Util.map_opt uu____7528
            (fun uu____7557  ->
               match uu____7557 with
               | (e0,b11,bvs) ->
                   let s1 bv =
                     let uu___1043_7579 = bv  in
                     let uu____7580 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___1043_7579.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___1043_7579.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____7580
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___1047_7588 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____7589 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____7598 =
                       let uu____7601 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____7601  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___1047_7588.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____7589;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____7598;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___1047_7588.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___1047_7588.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___1047_7588.FStar_Syntax_Syntax.ctx_uvar_range);
                       FStar_Syntax_Syntax.ctx_uvar_meta =
                         (uu___1047_7588.FStar_Syntax_Syntax.ctx_uvar_meta)
                     }  in
                   let uu___1050_7602 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1050_7602.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___1050_7602.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___1050_7602.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1050_7602.FStar_Tactics_Types.label)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____7613 =
      let uu____7616 = cur_goal ()  in
      bind uu____7616
        (fun goal  ->
           let uu____7624 = h  in
           match uu____7624 with
           | (bv,uu____7628) ->
               mlog
                 (fun uu____7636  ->
                    let uu____7637 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____7639 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____7637
                      uu____7639)
                 (fun uu____7644  ->
                    let uu____7645 =
                      let uu____7656 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____7656  in
                    match uu____7645 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                        let uu____7683 =
                          destruct_eq bv1.FStar_Syntax_Syntax.sort  in
                        (match uu____7683 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____7698 =
                               let uu____7699 = FStar_Syntax_Subst.compress x
                                  in
                               uu____7699.FStar_Syntax_Syntax.n  in
                             (match uu____7698 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv2 =
                                    let uu___1073_7716 = bv2  in
                                    let uu____7717 =
                                      FStar_Syntax_Subst.subst s
                                        bv2.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1073_7716.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1073_7716.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____7717
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv1 :: bvs1)  in
                                  let new_goal =
                                    let uu___1077_7725 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____7726 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____7735 =
                                      let uu____7738 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____7738
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___1077_7725.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____7726;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____7735;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___1077_7725.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___1077_7725.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___1077_7725.FStar_Syntax_Syntax.ctx_uvar_range);
                                      FStar_Syntax_Syntax.ctx_uvar_meta =
                                        (uu___1077_7725.FStar_Syntax_Syntax.ctx_uvar_meta)
                                    }  in
                                  replace_cur
                                    (let uu___1080_7741 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___1080_7741.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___1080_7741.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___1080_7741.FStar_Tactics_Types.is_guard);
                                       FStar_Tactics_Types.label =
                                         (uu___1080_7741.FStar_Tactics_Types.label)
                                     })
                              | uu____7742 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____7744 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____7613
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____7774 =
        let uu____7777 = cur_goal ()  in
        bind uu____7777
          (fun goal  ->
             let uu____7788 = b  in
             match uu____7788 with
             | (bv,uu____7792) ->
                 let bv' =
                   let uu____7798 =
                     let uu___1091_7799 = bv  in
                     let uu____7800 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____7800;
                       FStar_Syntax_Syntax.index =
                         (uu___1091_7799.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___1091_7799.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____7798  in
                 let s1 =
                   let uu____7805 =
                     let uu____7806 =
                       let uu____7813 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____7813)  in
                     FStar_Syntax_Syntax.NT uu____7806  in
                   [uu____7805]  in
                 let uu____7818 = subst_goal bv bv' s1 goal  in
                 (match uu____7818 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____7774
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____7840 =
      let uu____7843 = cur_goal ()  in
      bind uu____7843
        (fun goal  ->
           let uu____7852 = b  in
           match uu____7852 with
           | (bv,uu____7856) ->
               let uu____7861 =
                 let uu____7872 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____7872  in
               (match uu____7861 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                    let uu____7899 = FStar_Syntax_Util.type_u ()  in
                    (match uu____7899 with
                     | (ty,u) ->
                         let uu____7908 = new_uvar "binder_retype" e0 ty  in
                         bind uu____7908
                           (fun uu____7927  ->
                              match uu____7927 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___1115_7937 = bv1  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1115_7937.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1115_7937.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____7941 =
                                      let uu____7942 =
                                        let uu____7949 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv1, uu____7949)  in
                                      FStar_Syntax_Syntax.NT uu____7942  in
                                    [uu____7941]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___1120_7961 = b1  in
                                         let uu____7962 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___1120_7961.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___1120_7961.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____7962
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____7969  ->
                                       let new_goal =
                                         let uu____7971 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____7972 =
                                           let uu____7973 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____7973
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____7971 uu____7972
                                          in
                                       let uu____7974 = add_goals [new_goal]
                                          in
                                       bind uu____7974
                                         (fun uu____7979  ->
                                            let uu____7980 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv1.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____7980
                                              goal.FStar_Tactics_Types.opts
                                              goal.FStar_Tactics_Types.label))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____7840
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____8006 =
        let uu____8009 = cur_goal ()  in
        bind uu____8009
          (fun goal  ->
             let uu____8018 = b  in
             match uu____8018 with
             | (bv,uu____8022) ->
                 let uu____8027 =
                   let uu____8038 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____8038  in
                 (match uu____8027 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                      let steps =
                        let uu____8068 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____8068
                         in
                      let sort' =
                        normalize steps e0 bv1.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___1141_8073 = bv1  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___1141_8073.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___1141_8073.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____8075 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____8075))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____8006
  
let (revert : unit -> unit tac) =
  fun uu____8088  ->
    let uu____8091 = cur_goal ()  in
    bind uu____8091
      (fun goal  ->
         let uu____8097 =
           let uu____8104 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____8104  in
         match uu____8097 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____8121 =
                 let uu____8124 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____8124  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____8121
                in
             let uu____8139 = new_uvar "revert" env' typ'  in
             bind uu____8139
               (fun uu____8155  ->
                  match uu____8155 with
                  | (r,u_r) ->
                      let uu____8164 =
                        let uu____8167 =
                          let uu____8168 =
                            let uu____8169 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____8169.FStar_Syntax_Syntax.pos  in
                          let uu____8172 =
                            let uu____8177 =
                              let uu____8178 =
                                let uu____8187 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____8187  in
                              [uu____8178]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____8177  in
                          uu____8172 FStar_Pervasives_Native.None uu____8168
                           in
                        set_solution goal uu____8167  in
                      bind uu____8164
                        (fun uu____8206  ->
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
      let uu____8220 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____8220
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____8236 = cur_goal ()  in
    bind uu____8236
      (fun goal  ->
         mlog
           (fun uu____8244  ->
              let uu____8245 = FStar_Syntax_Print.binder_to_string b  in
              let uu____8247 =
                let uu____8249 =
                  let uu____8251 =
                    let uu____8260 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____8260  in
                  FStar_All.pipe_right uu____8251 FStar_List.length  in
                FStar_All.pipe_right uu____8249 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____8245 uu____8247)
           (fun uu____8281  ->
              let uu____8282 =
                let uu____8293 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____8293  in
              match uu____8282 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bv1,bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____8338 =
                          free_in bv1 bv'.FStar_Syntax_Syntax.sort  in
                        if uu____8338
                        then
                          let uu____8343 =
                            let uu____8345 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____8345
                             in
                          fail uu____8343
                        else check1 bvs2
                     in
                  let uu____8350 =
                    let uu____8352 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv1 uu____8352  in
                  if uu____8350
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____8359 = check1 bvs  in
                     bind uu____8359
                       (fun uu____8365  ->
                          let env' = push_bvs e' bvs  in
                          let uu____8367 =
                            let uu____8374 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____8374  in
                          bind uu____8367
                            (fun uu____8384  ->
                               match uu____8384 with
                               | (ut,uvar_ut) ->
                                   let uu____8393 = set_solution goal ut  in
                                   bind uu____8393
                                     (fun uu____8398  ->
                                        let uu____8399 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                            goal.FStar_Tactics_Types.label
                                           in
                                        replace_cur uu____8399))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____8407  ->
    let uu____8410 = cur_goal ()  in
    bind uu____8410
      (fun goal  ->
         let uu____8416 =
           let uu____8423 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____8423  in
         match uu____8416 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____8432) ->
             let uu____8437 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____8437)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____8450 = cur_goal ()  in
    bind uu____8450
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____8460 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____8460  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____8463  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____8476 = cur_goal ()  in
    bind uu____8476
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____8486 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____8486  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____8489  -> add_goals [g']))
  
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
            let uu____8530 = FStar_Syntax_Subst.compress t  in
            uu____8530.FStar_Syntax_Syntax.n  in
          let uu____8533 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___1325_8540 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___1325_8540.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___1325_8540.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____8533
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____8557 =
                   let uu____8558 = FStar_Syntax_Subst.compress t1  in
                   uu____8558.FStar_Syntax_Syntax.n  in
                 match uu____8557 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____8589 = ff hd1  in
                     bind uu____8589
                       (fun hd2  ->
                          let fa uu____8615 =
                            match uu____8615 with
                            | (a,q) ->
                                let uu____8636 = ff a  in
                                bind uu____8636 (fun a1  -> ret (a1, q))
                             in
                          let uu____8655 = mapM fa args  in
                          bind uu____8655
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____8737 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____8737 with
                      | (bs1,t') ->
                          let uu____8746 =
                            let uu____8749 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____8749 t'  in
                          bind uu____8746
                            (fun t''  ->
                               let uu____8753 =
                                 let uu____8754 =
                                   let uu____8773 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____8782 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____8773, uu____8782, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____8754  in
                               ret uu____8753))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____8857 = ff hd1  in
                     bind uu____8857
                       (fun hd2  ->
                          let ffb br =
                            let uu____8872 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____8872 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____8904 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____8904  in
                                let uu____8905 = ff1 e  in
                                bind uu____8905
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____8920 = mapM ffb brs  in
                          bind uu____8920
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____8964;
                          FStar_Syntax_Syntax.lbtyp = uu____8965;
                          FStar_Syntax_Syntax.lbeff = uu____8966;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____8968;
                          FStar_Syntax_Syntax.lbpos = uu____8969;_}::[]),e)
                     ->
                     let lb =
                       let uu____8997 =
                         let uu____8998 = FStar_Syntax_Subst.compress t1  in
                         uu____8998.FStar_Syntax_Syntax.n  in
                       match uu____8997 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____9002) -> lb
                       | uu____9018 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____9028 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____9028
                         (fun def1  ->
                            ret
                              (let uu___1278_9034 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1278_9034.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1278_9034.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1278_9034.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1278_9034.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1278_9034.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1278_9034.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____9035 = fflb lb  in
                     bind uu____9035
                       (fun lb1  ->
                          let uu____9045 =
                            let uu____9050 =
                              let uu____9051 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____9051]  in
                            FStar_Syntax_Subst.open_term uu____9050 e  in
                          match uu____9045 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____9081 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____9081  in
                              let uu____9082 = ff1 e1  in
                              bind uu____9082
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____9129 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____9129
                         (fun def  ->
                            ret
                              (let uu___1296_9135 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1296_9135.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1296_9135.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1296_9135.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1296_9135.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1296_9135.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1296_9135.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____9136 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____9136 with
                      | (lbs1,e1) ->
                          let uu____9151 = mapM fflb lbs1  in
                          bind uu____9151
                            (fun lbs2  ->
                               let uu____9163 = ff e1  in
                               bind uu____9163
                                 (fun e2  ->
                                    let uu____9171 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____9171 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____9242 = ff t2  in
                     bind uu____9242
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____9273 = ff t2  in
                     bind uu____9273
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____9280 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___1320_9287 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___1320_9287.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___1320_9287.FStar_Syntax_Syntax.vars)
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
              let uu____9334 =
                FStar_TypeChecker_TcTerm.tc_term
                  (let uu___1333_9343 = env  in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___1333_9343.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___1333_9343.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___1333_9343.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___1333_9343.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_sig =
                       (uu___1333_9343.FStar_TypeChecker_Env.gamma_sig);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___1333_9343.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___1333_9343.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___1333_9343.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___1333_9343.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.attrtab =
                       (uu___1333_9343.FStar_TypeChecker_Env.attrtab);
                     FStar_TypeChecker_Env.is_pattern =
                       (uu___1333_9343.FStar_TypeChecker_Env.is_pattern);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___1333_9343.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___1333_9343.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___1333_9343.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___1333_9343.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___1333_9343.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___1333_9343.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___1333_9343.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___1333_9343.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___1333_9343.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax = true;
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___1333_9343.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.phase1 =
                       (uu___1333_9343.FStar_TypeChecker_Env.phase1);
                     FStar_TypeChecker_Env.failhard =
                       (uu___1333_9343.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___1333_9343.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.uvar_subtyping =
                       (uu___1333_9343.FStar_TypeChecker_Env.uvar_subtyping);
                     FStar_TypeChecker_Env.tc_term =
                       (uu___1333_9343.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.type_of =
                       (uu___1333_9343.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___1333_9343.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.check_type_of =
                       (uu___1333_9343.FStar_TypeChecker_Env.check_type_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___1333_9343.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (uu___1333_9343.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (uu___1333_9343.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.fv_delta_depths =
                       (uu___1333_9343.FStar_TypeChecker_Env.fv_delta_depths);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___1333_9343.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (uu___1333_9343.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.splice =
                       (uu___1333_9343.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.postprocess =
                       (uu___1333_9343.FStar_TypeChecker_Env.postprocess);
                     FStar_TypeChecker_Env.is_native_tactic =
                       (uu___1333_9343.FStar_TypeChecker_Env.is_native_tactic);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___1333_9343.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (uu___1333_9343.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (uu___1333_9343.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.nbe =
                       (uu___1333_9343.FStar_TypeChecker_Env.nbe)
                   }) t
                 in
              match uu____9334 with
              | (t1,lcomp,g) ->
                  let uu____9350 =
                    (let uu____9354 =
                       FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                     Prims.op_Negation uu____9354) ||
                      (let uu____9357 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____9357)
                     in
                  if uu____9350
                  then ret t1
                  else
                    (let rewrite_eq =
                       let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                       let uu____9368 = new_uvar "pointwise_rec" env typ  in
                       bind uu____9368
                         (fun uu____9385  ->
                            match uu____9385 with
                            | (ut,uvar_ut) ->
                                (log ps
                                   (fun uu____9398  ->
                                      let uu____9399 =
                                        FStar_Syntax_Print.term_to_string t1
                                         in
                                      let uu____9401 =
                                        FStar_Syntax_Print.term_to_string ut
                                         in
                                      FStar_Util.print2
                                        "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                        uu____9399 uu____9401);
                                 (let uu____9404 =
                                    let uu____9407 =
                                      let uu____9408 =
                                        FStar_TypeChecker_TcTerm.universe_of
                                          env typ
                                         in
                                      FStar_Syntax_Util.mk_eq2 uu____9408 typ
                                        t1 ut
                                       in
                                    add_irrelevant_goal
                                      "pointwise_rec equation" env uu____9407
                                      opts label1
                                     in
                                  bind uu____9404
                                    (fun uu____9412  ->
                                       let uu____9413 =
                                         bind tau
                                           (fun uu____9419  ->
                                              let ut1 =
                                                FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                  env ut
                                                 in
                                              log ps
                                                (fun uu____9425  ->
                                                   let uu____9426 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1
                                                      in
                                                   let uu____9428 =
                                                     FStar_Syntax_Print.term_to_string
                                                       ut1
                                                      in
                                                   FStar_Util.print2
                                                     "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                     uu____9426 uu____9428);
                                              ret ut1)
                                          in
                                       focus uu____9413))))
                        in
                     let uu____9431 = catch rewrite_eq  in
                     bind uu____9431
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
          let uu____9643 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____9643
            (fun t1  ->
               let uu____9651 =
                 f env
                   (let uu___1410_9659 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___1410_9659.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___1410_9659.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____9651
                 (fun uu____9675  ->
                    match uu____9675 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____9698 =
                               let uu____9699 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____9699.FStar_Syntax_Syntax.n  in
                             match uu____9698 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____9736 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____9736
                                   (fun uu____9758  ->
                                      match uu____9758 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____9774 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____9774
                                            (fun uu____9798  ->
                                               match uu____9798 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___1390_9828 =
                                                         t3  in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___1390_9828.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___1390_9828.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____9870 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____9870 with
                                  | (bs1,t') ->
                                      let uu____9885 =
                                        let uu____9892 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____9892 ctrl1 t'
                                         in
                                      bind uu____9885
                                        (fun uu____9907  ->
                                           match uu____9907 with
                                           | (t'',ctrl2) ->
                                               let uu____9922 =
                                                 let uu____9929 =
                                                   let uu___1403_9932 = t4
                                                      in
                                                   let uu____9935 =
                                                     let uu____9936 =
                                                       let uu____9955 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____9964 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____9955,
                                                         uu____9964, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____9936
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____9935;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___1403_9932.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___1403_9932.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____9929, ctrl2)  in
                                               ret uu____9922))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____10017 -> ret (t3, ctrl1))))

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
              let uu____10063 = ctrl_tac_fold f env ctrl t  in
              bind uu____10063
                (fun uu____10084  ->
                   match uu____10084 with
                   | (t1,ctrl1) ->
                       let uu____10099 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____10099
                         (fun uu____10123  ->
                            match uu____10123 with
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
                let uu____10214 =
                  let uu____10222 =
                    add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                      opts label1
                     in
                  bind uu____10222
                    (fun uu____10233  ->
                       let uu____10234 = ctrl t1  in
                       bind uu____10234
                         (fun res  ->
                            let uu____10260 = trivial ()  in
                            bind uu____10260 (fun uu____10269  -> ret res)))
                   in
                bind uu____10214
                  (fun uu____10287  ->
                     match uu____10287 with
                     | (should_rewrite,ctrl1) ->
                         if Prims.op_Negation should_rewrite
                         then ret (t1, ctrl1)
                         else
                           (let uu____10316 =
                              FStar_TypeChecker_TcTerm.tc_term
                                (let uu___1440_10325 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___1440_10325.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___1440_10325.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___1440_10325.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___1440_10325.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___1440_10325.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___1440_10325.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___1440_10325.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___1440_10325.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___1440_10325.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___1440_10325.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___1440_10325.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___1440_10325.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___1440_10325.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___1440_10325.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___1440_10325.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___1440_10325.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___1440_10325.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___1440_10325.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___1440_10325.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___1440_10325.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___1440_10325.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___1440_10325.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___1440_10325.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___1440_10325.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___1440_10325.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___1440_10325.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___1440_10325.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___1440_10325.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___1440_10325.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___1440_10325.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___1440_10325.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___1440_10325.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___1440_10325.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___1440_10325.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___1440_10325.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___1440_10325.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___1440_10325.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___1440_10325.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___1440_10325.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___1440_10325.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___1440_10325.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___1440_10325.FStar_TypeChecker_Env.nbe)
                                 }) t1
                               in
                            match uu____10316 with
                            | (t2,lcomp,g) ->
                                let uu____10336 =
                                  (let uu____10340 =
                                     FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                       lcomp
                                      in
                                   Prims.op_Negation uu____10340) ||
                                    (let uu____10343 =
                                       FStar_TypeChecker_Env.is_trivial g  in
                                     Prims.op_Negation uu____10343)
                                   in
                                if uu____10336
                                then ret (t2, globalStop)
                                else
                                  (let typ =
                                     lcomp.FStar_Syntax_Syntax.res_typ  in
                                   let uu____10359 =
                                     new_uvar "pointwise_rec" env typ  in
                                   bind uu____10359
                                     (fun uu____10380  ->
                                        match uu____10380 with
                                        | (ut,uvar_ut) ->
                                            (log ps
                                               (fun uu____10397  ->
                                                  let uu____10398 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t2
                                                     in
                                                  let uu____10400 =
                                                    FStar_Syntax_Print.term_to_string
                                                      ut
                                                     in
                                                  FStar_Util.print2
                                                    "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                    uu____10398 uu____10400);
                                             (let uu____10403 =
                                                let uu____10406 =
                                                  let uu____10407 =
                                                    FStar_TypeChecker_TcTerm.universe_of
                                                      env typ
                                                     in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____10407 typ t2 ut
                                                   in
                                                add_irrelevant_goal
                                                  "rewrite_rec equation" env
                                                  uu____10406 opts label1
                                                 in
                                              bind uu____10403
                                                (fun uu____10415  ->
                                                   let uu____10416 =
                                                     bind rewriter
                                                       (fun uu____10430  ->
                                                          let ut1 =
                                                            FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                              env ut
                                                             in
                                                          log ps
                                                            (fun uu____10436 
                                                               ->
                                                               let uu____10437
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   t2
                                                                  in
                                                               let uu____10439
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   ut1
                                                                  in
                                                               FStar_Util.print2
                                                                 "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                                 uu____10437
                                                                 uu____10439);
                                                          ret (ut1, ctrl1))
                                                      in
                                                   focus uu____10416)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term -> (Prims.bool * FStar_BigInt.t) tac) ->
    unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____10484 =
        bind get
          (fun ps  ->
             let uu____10494 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____10494 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____10532  ->
                       let uu____10533 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____10533);
                  bind dismiss_all
                    (fun uu____10538  ->
                       let uu____10539 =
                         let uu____10546 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____10546
                           keepGoing gt1
                          in
                       bind uu____10539
                         (fun uu____10556  ->
                            match uu____10556 with
                            | (gt',uu____10564) ->
                                (log ps
                                   (fun uu____10568  ->
                                      let uu____10569 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____10569);
                                 (let uu____10572 = push_goals gs  in
                                  bind uu____10572
                                    (fun uu____10577  ->
                                       let uu____10578 =
                                         let uu____10581 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____10581]  in
                                       add_goals uu____10578)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____10484
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____10606 =
        bind get
          (fun ps  ->
             let uu____10616 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____10616 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____10654  ->
                       let uu____10655 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____10655);
                  bind dismiss_all
                    (fun uu____10660  ->
                       let uu____10661 =
                         let uu____10664 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____10664 gt1
                          in
                       bind uu____10661
                         (fun gt'  ->
                            log ps
                              (fun uu____10672  ->
                                 let uu____10673 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____10673);
                            (let uu____10676 = push_goals gs  in
                             bind uu____10676
                               (fun uu____10681  ->
                                  let uu____10682 =
                                    let uu____10685 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____10685]  in
                                  add_goals uu____10682))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____10606
  
let (trefl : unit -> unit tac) =
  fun uu____10698  ->
    let uu____10701 =
      let uu____10704 = cur_goal ()  in
      bind uu____10704
        (fun g  ->
           let uu____10722 =
             let uu____10727 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____10727  in
           match uu____10722 with
           | FStar_Pervasives_Native.Some t ->
               let uu____10735 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____10735 with
                | (hd1,args) ->
                    let uu____10774 =
                      let uu____10787 =
                        let uu____10788 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____10788.FStar_Syntax_Syntax.n  in
                      (uu____10787, args)  in
                    (match uu____10774 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____10802::(l,uu____10804)::(r,uu____10806)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____10853 =
                           let uu____10857 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____10857 l r  in
                         bind uu____10853
                           (fun b  ->
                              if b
                              then solve' g FStar_Syntax_Util.exp_unit
                              else
                                (let l1 =
                                   let uu____10868 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____10868 l
                                    in
                                 let r1 =
                                   let uu____10870 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____10870 r
                                    in
                                 let uu____10871 =
                                   let uu____10875 =
                                     FStar_Tactics_Types.goal_env g  in
                                   do_unify uu____10875 l1 r1  in
                                 bind uu____10871
                                   (fun b1  ->
                                      if b1
                                      then
                                        solve' g FStar_Syntax_Util.exp_unit
                                      else
                                        (let uu____10885 =
                                           let uu____10887 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____10887 l1  in
                                         let uu____10888 =
                                           let uu____10890 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____10890 r1  in
                                         fail2
                                           "not a trivial equality ((%s) vs (%s))"
                                           uu____10885 uu____10888))))
                     | (hd2,uu____10893) ->
                         let uu____10910 =
                           let uu____10912 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____10912 t  in
                         fail1 "trefl: not an equality (%s)" uu____10910))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____10701
  
let (dup : unit -> unit tac) =
  fun uu____10929  ->
    let uu____10932 = cur_goal ()  in
    bind uu____10932
      (fun g  ->
         let uu____10938 =
           let uu____10945 = FStar_Tactics_Types.goal_env g  in
           let uu____10946 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____10945 uu____10946  in
         bind uu____10938
           (fun uu____10956  ->
              match uu____10956 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___1532_10966 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___1532_10966.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___1532_10966.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___1532_10966.FStar_Tactics_Types.is_guard);
                      FStar_Tactics_Types.label =
                        (uu___1532_10966.FStar_Tactics_Types.label)
                    }  in
                  bind __dismiss
                    (fun uu____10969  ->
                       let uu____10970 =
                         let uu____10973 = FStar_Tactics_Types.goal_env g  in
                         let uu____10974 =
                           let uu____10975 =
                             let uu____10976 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____10977 =
                               FStar_Tactics_Types.goal_type g  in
                             FStar_TypeChecker_TcTerm.universe_of uu____10976
                               uu____10977
                              in
                           let uu____10978 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____10979 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____10975 uu____10978 u
                             uu____10979
                            in
                         add_irrelevant_goal "dup equation" uu____10973
                           uu____10974 g.FStar_Tactics_Types.opts
                           g.FStar_Tactics_Types.label
                          in
                       bind uu____10970
                         (fun uu____10983  ->
                            let uu____10984 = add_goals [g']  in
                            bind uu____10984 (fun uu____10988  -> ret ())))))
  
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
              let uu____11114 = f x y  in
              if uu____11114 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____11137 -> (acc, l11, l21)  in
        let uu____11152 = aux [] l1 l2  in
        match uu____11152 with | (pr,t1,t2) -> ((FStar_List.rev pr), t1, t2)
  
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
      let uu____11258 = get_phi g1  in
      match uu____11258 with
      | FStar_Pervasives_Native.None  -> fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____11265 = get_phi g2  in
          (match uu____11265 with
           | FStar_Pervasives_Native.None  -> fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let uu____11278 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2)
                  in
               (match uu____11278 with
                | (gamma,r1,r2) ->
                    let t1 =
                      let uu____11309 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1)
                         in
                      close_forall_no_univs1 uu____11309 phi1  in
                    let t2 =
                      let uu____11319 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2)
                         in
                      close_forall_no_univs1 uu____11319 phi2  in
                    let uu____11328 =
                      set_solution g1 FStar_Syntax_Util.exp_unit  in
                    bind uu____11328
                      (fun uu____11333  ->
                         let uu____11334 =
                           set_solution g2 FStar_Syntax_Util.exp_unit  in
                         bind uu____11334
                           (fun uu____11341  ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2  in
                              let nenv =
                                let uu___1583_11346 =
                                  FStar_Tactics_Types.goal_env g1  in
                                let uu____11347 =
                                  FStar_Util.smap_create
                                    (Prims.parse_int "100")
                                   in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___1583_11346.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___1583_11346.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___1583_11346.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___1583_11346.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____11347;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___1583_11346.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___1583_11346.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___1583_11346.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___1583_11346.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___1583_11346.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___1583_11346.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___1583_11346.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___1583_11346.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___1583_11346.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___1583_11346.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___1583_11346.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___1583_11346.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___1583_11346.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___1583_11346.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___1583_11346.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___1583_11346.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___1583_11346.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___1583_11346.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___1583_11346.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___1583_11346.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___1583_11346.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___1583_11346.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___1583_11346.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___1583_11346.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___1583_11346.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___1583_11346.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___1583_11346.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___1583_11346.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___1583_11346.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___1583_11346.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___1583_11346.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___1583_11346.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___1583_11346.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___1583_11346.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___1583_11346.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___1583_11346.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___1583_11346.FStar_TypeChecker_Env.nbe)
                                }  in
                              let uu____11351 =
                                mk_irrelevant_goal "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                  g1.FStar_Tactics_Types.label
                                 in
                              bind uu____11351
                                (fun goal  ->
                                   mlog
                                     (fun uu____11361  ->
                                        let uu____11362 =
                                          goal_to_string_verbose g1  in
                                        let uu____11364 =
                                          goal_to_string_verbose g2  in
                                        let uu____11366 =
                                          goal_to_string_verbose goal  in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____11362 uu____11364 uu____11366)
                                     (fun uu____11370  -> ret goal))))))
  
let (join : unit -> unit tac) =
  fun uu____11378  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____11394 =
               set
                 (let uu___1598_11399 = ps  in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___1598_11399.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.main_goal =
                      (uu___1598_11399.FStar_Tactics_Types.main_goal);
                    FStar_Tactics_Types.all_implicits =
                      (uu___1598_11399.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___1598_11399.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___1598_11399.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___1598_11399.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___1598_11399.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___1598_11399.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___1598_11399.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___1598_11399.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___1598_11399.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___1598_11399.FStar_Tactics_Types.local_state)
                  })
                in
             bind uu____11394
               (fun uu____11402  ->
                  let uu____11403 = join_goals g1 g2  in
                  bind uu____11403 (fun g12  -> add_goals [g12]))
         | uu____11408 -> fail "join: less than 2 goals")
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____11424 =
      let uu____11427 = cur_goal ()  in
      bind uu____11427
        (fun g  ->
           FStar_Options.push ();
           (let uu____11440 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____11440);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___1609_11447 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1609_11447.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___1609_11447.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___1609_11447.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1609_11447.FStar_Tactics_Types.label)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____11424
  
let (top_env : unit -> env tac) =
  fun uu____11464  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____11479  ->
    let uu____11483 = cur_goal ()  in
    bind uu____11483
      (fun g  ->
         let uu____11490 =
           (FStar_Options.lax ()) ||
             (let uu____11493 = FStar_Tactics_Types.goal_env g  in
              uu____11493.FStar_TypeChecker_Env.lax)
            in
         ret uu____11490)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____11510 =
        mlog
          (fun uu____11515  ->
             let uu____11516 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____11516)
          (fun uu____11521  ->
             let uu____11522 = cur_goal ()  in
             bind uu____11522
               (fun goal  ->
                  let env =
                    let uu____11530 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____11530 ty  in
                  let uu____11531 = __tc_ghost env tm  in
                  bind uu____11531
                    (fun uu____11550  ->
                       match uu____11550 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____11564  ->
                                let uu____11565 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____11565)
                             (fun uu____11569  ->
                                mlog
                                  (fun uu____11572  ->
                                     let uu____11573 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____11573)
                                  (fun uu____11578  ->
                                     let uu____11579 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____11579
                                       (fun uu____11584  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____11510
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____11609 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____11615 =
              let uu____11622 =
                let uu____11623 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____11623
                 in
              new_uvar "uvar_env.2" env uu____11622  in
            bind uu____11615
              (fun uu____11640  ->
                 match uu____11640 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____11609
        (fun typ  ->
           let uu____11652 = new_uvar "uvar_env" env typ  in
           bind uu____11652
             (fun uu____11667  ->
                match uu____11667 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____11686 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____11705 -> g.FStar_Tactics_Types.opts
             | uu____11708 -> FStar_Options.peek ()  in
           let uu____11711 = FStar_Syntax_Util.head_and_args t  in
           match uu____11711 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____11731);
                FStar_Syntax_Syntax.pos = uu____11732;
                FStar_Syntax_Syntax.vars = uu____11733;_},uu____11734)
               ->
               let env1 =
                 let uu___1663_11776 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___1663_11776.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___1663_11776.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___1663_11776.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___1663_11776.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___1663_11776.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___1663_11776.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___1663_11776.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___1663_11776.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___1663_11776.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___1663_11776.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___1663_11776.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___1663_11776.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___1663_11776.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___1663_11776.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___1663_11776.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___1663_11776.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___1663_11776.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___1663_11776.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___1663_11776.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___1663_11776.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___1663_11776.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___1663_11776.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___1663_11776.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___1663_11776.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___1663_11776.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___1663_11776.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___1663_11776.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___1663_11776.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___1663_11776.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___1663_11776.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___1663_11776.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___1663_11776.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___1663_11776.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___1663_11776.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___1663_11776.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___1663_11776.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___1663_11776.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___1663_11776.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___1663_11776.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___1663_11776.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___1663_11776.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___1663_11776.FStar_TypeChecker_Env.nbe)
                 }  in
               let g =
                 FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false ""  in
               let uu____11780 =
                 let uu____11783 = bnorm_goal g  in [uu____11783]  in
               add_goals uu____11780
           | uu____11784 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____11686
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____11846 = if b then t2 else ret false  in
             bind uu____11846 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____11872 = trytac comp  in
      bind uu____11872
        (fun uu___4_11884  ->
           match uu___4_11884 with
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
        let uu____11926 =
          bind get
            (fun ps  ->
               let uu____11934 = __tc e t1  in
               bind uu____11934
                 (fun uu____11955  ->
                    match uu____11955 with
                    | (t11,ty1,g1) ->
                        let uu____11968 = __tc e t2  in
                        bind uu____11968
                          (fun uu____11989  ->
                             match uu____11989 with
                             | (t21,ty2,g2) ->
                                 let uu____12002 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____12002
                                   (fun uu____12009  ->
                                      let uu____12010 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____12010
                                        (fun uu____12018  ->
                                           let uu____12019 =
                                             do_unify e ty1 ty2  in
                                           let uu____12023 =
                                             do_unify e t11 t21  in
                                           tac_and uu____12019 uu____12023)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____11926
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____12071  ->
             let uu____12072 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____12072
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
        (fun uu____12106  ->
           let uu____12107 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____12107)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____12118 =
      mlog
        (fun uu____12123  ->
           let uu____12124 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____12124)
        (fun uu____12129  ->
           let uu____12130 = cur_goal ()  in
           bind uu____12130
             (fun g  ->
                let uu____12136 =
                  let uu____12145 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____12145 ty  in
                bind uu____12136
                  (fun uu____12157  ->
                     match uu____12157 with
                     | (ty1,uu____12167,guard) ->
                         let uu____12169 =
                           let uu____12172 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____12172 guard  in
                         bind uu____12169
                           (fun uu____12176  ->
                              let uu____12177 =
                                let uu____12181 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____12182 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____12181 uu____12182 ty1  in
                              bind uu____12177
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____12191 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____12191
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops]  in
                                      let ng =
                                        let uu____12198 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____12199 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____12198
                                          uu____12199
                                         in
                                      let nty =
                                        let uu____12201 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____12201 ty1  in
                                      let uu____12202 =
                                        let uu____12206 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____12206 ng nty  in
                                      bind uu____12202
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____12215 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____12215
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____12118
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) Prims.list tac)
  =
  fun s_tm  ->
    let uu____12289 =
      let uu____12298 = cur_goal ()  in
      bind uu____12298
        (fun g  ->
           let uu____12310 =
             let uu____12319 = FStar_Tactics_Types.goal_env g  in
             __tc uu____12319 s_tm  in
           bind uu____12310
             (fun uu____12337  ->
                match uu____12337 with
                | (s_tm1,s_ty,guard) ->
                    let uu____12355 =
                      let uu____12358 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____12358 guard  in
                    bind uu____12355
                      (fun uu____12371  ->
                         let uu____12372 =
                           FStar_Syntax_Util.head_and_args' s_ty  in
                         match uu____12372 with
                         | (h,args) ->
                             let uu____12417 =
                               let uu____12424 =
                                 let uu____12425 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____12425.FStar_Syntax_Syntax.n  in
                               match uu____12424 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____12440;
                                      FStar_Syntax_Syntax.vars = uu____12441;_},us)
                                   -> ret (fv, us)
                               | uu____12451 -> fail "type is not an fv"  in
                             bind uu____12417
                               (fun uu____12472  ->
                                  match uu____12472 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____12488 =
                                        let uu____12491 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____12491 t_lid
                                         in
                                      (match uu____12488 with
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
                                                  (fun uu____12542  ->
                                                     let uu____12543 =
                                                       FStar_Syntax_Subst.open_term
                                                         t_ps t_ty
                                                        in
                                                     match uu____12543 with
                                                     | (t_ps1,t_ty1) ->
                                                         let uu____12558 =
                                                           mapM
                                                             (fun c_lid  ->
                                                                let uu____12586
                                                                  =
                                                                  let uu____12589
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                  FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____12589
                                                                    c_lid
                                                                   in
                                                                match uu____12586
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
                                                                    uu____12663
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
                                                                    let uu____12668
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____12668
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____12691
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____12691
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____12734
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs
                                                                     in
                                                                    (match uu____12734
                                                                    with
                                                                    | 
                                                                    (d_ps,bs1)
                                                                    ->
                                                                    let uu____12807
                                                                    =
                                                                    let uu____12809
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp  in
                                                                    Prims.op_Negation
                                                                    uu____12809
                                                                     in
                                                                    failwhen
                                                                    uu____12807
                                                                    "not total?"
                                                                    (fun
                                                                    uu____12828
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
                                                                    uu___5_12845
                                                                    =
                                                                    match uu___5_12845
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____12849)
                                                                    -> true
                                                                    | 
                                                                    uu____12852
                                                                    -> false
                                                                     in
                                                                    let uu____12856
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____12856
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
                                                                    uu____12990
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
                                                                    uu____13052
                                                                     ->
                                                                    match uu____13052
                                                                    with
                                                                    | 
                                                                    ((bv,uu____13072),
                                                                    (t,uu____13074))
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
                                                                    uu____13144
                                                                     ->
                                                                    match uu____13144
                                                                    with
                                                                    | 
                                                                    ((bv,uu____13171),
                                                                    (t,uu____13173))
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
                                                                    uu____13232
                                                                     ->
                                                                    match uu____13232
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
                                                                    let uu____13287
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___1827_13304
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___1827_13304.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1827_13304.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1827_13304.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___1827_13304.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___1827_13304.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1827_13304.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1827_13304.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1827_13304.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1827_13304.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___1827_13304.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___1827_13304.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___1827_13304.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1827_13304.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1827_13304.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1827_13304.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1827_13304.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1827_13304.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1827_13304.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1827_13304.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___1827_13304.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___1827_13304.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1827_13304.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1827_13304.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1827_13304.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1827_13304.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1827_13304.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1827_13304.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1827_13304.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1827_13304.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1827_13304.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1827_13304.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1827_13304.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1827_13304.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1827_13304.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___1827_13304.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1827_13304.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1827_13304.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___1827_13304.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1827_13304.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1827_13304.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1827_13304.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1827_13304.FStar_TypeChecker_Env.nbe)
                                                                    }) s_ty
                                                                    pat  in
                                                                    match uu____13287
                                                                    with
                                                                    | 
                                                                    (uu____13318,uu____13319,uu____13320,pat_t,uu____13322,_guard_pat)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____13329
                                                                    =
                                                                    let uu____13330
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____13330
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____13329
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____13335
                                                                    =
                                                                    let uu____13344
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____13344]
                                                                     in
                                                                    let uu____13363
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____13335
                                                                    uu____13363
                                                                     in
                                                                    let nty =
                                                                    let uu____13369
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____13369
                                                                     in
                                                                    let uu____13372
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____13372
                                                                    (fun
                                                                    uu____13402
                                                                     ->
                                                                    match uu____13402
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
                                                                    let uu____13429
                                                                    =
                                                                    let uu____13440
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____13440]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____13429
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____13476
                                                                    =
                                                                    let uu____13487
                                                                    =
                                                                    let uu____13492
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2)  in
                                                                    (fv1,
                                                                    uu____13492)
                                                                     in
                                                                    (g', br,
                                                                    uu____13487)
                                                                     in
                                                                    ret
                                                                    uu____13476))))))
                                                                    | 
                                                                    uu____13513
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                             c_lids
                                                            in
                                                         bind uu____12558
                                                           (fun goal_brs  ->
                                                              let uu____13563
                                                                =
                                                                FStar_List.unzip3
                                                                  goal_brs
                                                                 in
                                                              match uu____13563
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
                                                                  let uu____13636
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                  bind
                                                                    uu____13636
                                                                    (
                                                                    fun
                                                                    uu____13647
                                                                     ->
                                                                    let uu____13648
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____13648
                                                                    (fun
                                                                    uu____13658
                                                                     ->
                                                                    ret infos))))
                                            | uu____13665 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____12289
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____13714::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____13744 = init xs  in x :: uu____13744
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____13757 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      let t3 = FStar_Syntax_Util.unlazy_emb t2  in
      match t3.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____13766) -> inspect t4
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____13832 = last args  in
          (match uu____13832 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____13862 =
                 let uu____13863 =
                   let uu____13868 =
                     let uu____13869 =
                       let uu____13874 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____13874  in
                     uu____13869 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____13868, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____13863  in
               FStar_All.pipe_left ret uu____13862)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____13885,uu____13886) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
          let uu____13939 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____13939 with
           | (bs1,t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____13981 =
                      let uu____13982 =
                        let uu____13987 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____13987)  in
                      FStar_Reflection_Data.Tv_Abs uu____13982  in
                    FStar_All.pipe_left ret uu____13981))
      | FStar_Syntax_Syntax.Tm_type uu____13990 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____14015 ->
          let uu____14030 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____14030 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____14061 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____14061 with
           | (b',t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____14114 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____14127 =
            let uu____14128 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____14128  in
          FStar_All.pipe_left ret uu____14127
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____14149 =
            let uu____14150 =
              let uu____14155 =
                let uu____14156 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____14156  in
              (uu____14155, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____14150  in
          FStar_All.pipe_left ret uu____14149
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____14196 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____14201 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____14201 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____14254 ->
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
             | FStar_Util.Inr uu____14296 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____14300 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____14300 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____14320 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____14326 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____14381 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____14381
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____14402 =
                  let uu____14409 =
                    FStar_List.map
                      (fun uu____14422  ->
                         match uu____14422 with
                         | (p1,uu____14431) -> inspect_pat p1) ps
                     in
                  (fv, uu____14409)  in
                FStar_Reflection_Data.Pat_Cons uu____14402
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
              (fun uu___6_14527  ->
                 match uu___6_14527 with
                 | (pat,uu____14549,t5) ->
                     let uu____14567 = inspect_pat pat  in (uu____14567, t5))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____14576 ->
          ((let uu____14578 =
              let uu____14584 =
                let uu____14586 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____14588 = FStar_Syntax_Print.term_to_string t3  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____14586 uu____14588
                 in
              (FStar_Errors.Warning_CantInspect, uu____14584)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____14578);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____13757
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____14606 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____14606
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____14610 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____14610
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____14614 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____14614
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____14621 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____14621
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____14646 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____14646
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____14663 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____14663
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____14682 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____14682
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____14686 =
          let uu____14687 =
            let uu____14694 =
              let uu____14695 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____14695  in
            FStar_Syntax_Syntax.mk uu____14694  in
          uu____14687 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____14686
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____14700 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____14700
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____14711 =
          let uu____14712 =
            let uu____14719 =
              let uu____14720 =
                let uu____14734 =
                  let uu____14737 =
                    let uu____14738 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____14738]  in
                  FStar_Syntax_Subst.close uu____14737 t2  in
                ((false, [lb]), uu____14734)  in
              FStar_Syntax_Syntax.Tm_let uu____14720  in
            FStar_Syntax_Syntax.mk uu____14719  in
          uu____14712 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____14711
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____14780 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____14780 with
         | (lbs,body) ->
             let uu____14795 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____14795)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____14832 =
                let uu____14833 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____14833  in
              FStar_All.pipe_left wrap uu____14832
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____14840 =
                let uu____14841 =
                  let uu____14855 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____14873 = pack_pat p1  in
                         (uu____14873, false)) ps
                     in
                  (fv, uu____14855)  in
                FStar_Syntax_Syntax.Pat_cons uu____14841  in
              FStar_All.pipe_left wrap uu____14840
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
            (fun uu___7_14922  ->
               match uu___7_14922 with
               | (pat,t1) ->
                   let uu____14939 = pack_pat pat  in
                   (uu____14939, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____14987 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____14987
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____15015 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15015
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____15061 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15061
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____15100 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15100
  
let (lget :
  FStar_Reflection_Data.typ -> Prims.string -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun k  ->
      let uu____15120 =
        bind get
          (fun ps  ->
             let uu____15126 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____15126 with
             | FStar_Pervasives_Native.None  -> fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
      FStar_All.pipe_left (wrap_err "lget") uu____15120
  
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit tac)
  =
  fun _ty  ->
    fun k  ->
      fun t  ->
        let uu____15160 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___2125_15167 = ps  in
                 let uu____15168 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t
                    in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___2125_15167.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___2125_15167.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___2125_15167.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___2125_15167.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___2125_15167.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___2125_15167.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___2125_15167.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___2125_15167.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___2125_15167.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___2125_15167.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___2125_15167.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___2125_15167.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____15168
                 }  in
               set ps1)
           in
        FStar_All.pipe_left (wrap_err "lset") uu____15160
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal * FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun typ  ->
      let uu____15195 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____15195 with
      | (u,ctx_uvars,g_u) ->
          let uu____15228 = FStar_List.hd ctx_uvars  in
          (match uu____15228 with
           | (ctx_uvar,uu____15242) ->
               let g =
                 let uu____15244 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____15244 false
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
        let uu____15267 = goal_of_goal_ty env typ  in
        match uu____15267 with
        | (g,g_u) ->
            let ps =
              let uu____15279 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "TacVerbose")
                 in
              let uu____15282 = FStar_Util.psmap_empty ()  in
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
                FStar_Tactics_Types.tac_verb_dbg = uu____15279;
                FStar_Tactics_Types.local_state = uu____15282
              }  in
            let uu____15292 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____15292)
  