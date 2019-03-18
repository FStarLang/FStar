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
    let uu____63873 =
      let uu____63874 = FStar_Tactics_Types.goal_env g  in
      let uu____63875 = FStar_Tactics_Types.goal_type g  in
      bnorm uu____63874 uu____63875  in
    FStar_Tactics_Types.goal_with_type g uu____63873
  
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
      let uu____63989 = FStar_Options.tactics_failhard ()  in
      if uu____63989
      then run t p
      else
        (try (fun uu___640_63999  -> match () with | () -> run t p) ()
         with
         | FStar_Errors.Err (uu____64008,msg) ->
             FStar_Tactics_Result.Failed
               ((FStar_Tactics_Types.TacticFailure msg), p)
         | FStar_Errors.Error (uu____64012,msg,uu____64014) ->
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
           let uu____64094 = run t1 p  in
           match uu____64094 with
           | FStar_Tactics_Result.Success (a,q) ->
               let uu____64101 = t2 a  in run uu____64101 q
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
    let uu____64124 =
      FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head  in
    match uu____64124 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (check_goal_solved :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun goal  -> get_uvar_solved goal.FStar_Tactics_Types.goal_ctx_uvar 
let (goal_to_string_verbose : FStar_Tactics_Types.goal -> Prims.string) =
  fun g  ->
    let uu____64146 =
      FStar_Syntax_Print.ctx_uvar_to_string
        g.FStar_Tactics_Types.goal_ctx_uvar
       in
    let uu____64148 =
      let uu____64150 = check_goal_solved g  in
      match uu____64150 with
      | FStar_Pervasives_Native.None  -> ""
      | FStar_Pervasives_Native.Some t ->
          let uu____64156 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "\tGOAL ALREADY SOLVED!: %s" uu____64156
       in
    FStar_Util.format2 "%s%s\n" uu____64146 uu____64148
  
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
            let uu____64203 = FStar_Options.print_implicits ()  in
            if uu____64203
            then
              let uu____64207 = FStar_Tactics_Types.goal_env g  in
              let uu____64208 = FStar_Tactics_Types.goal_witness g  in
              tts uu____64207 uu____64208
            else
              (let uu____64211 =
                 get_uvar_solved g.FStar_Tactics_Types.goal_ctx_uvar  in
               match uu____64211 with
               | FStar_Pervasives_Native.None  -> "_"
               | FStar_Pervasives_Native.Some t ->
                   let uu____64217 = FStar_Tactics_Types.goal_env g  in
                   let uu____64218 = FStar_Tactics_Types.goal_witness g  in
                   tts uu____64217 uu____64218)
             in
          let num =
            match maybe_num with
            | FStar_Pervasives_Native.None  -> ""
            | FStar_Pervasives_Native.Some (i,n1) ->
                let uu____64241 = FStar_Util.string_of_int i  in
                let uu____64243 = FStar_Util.string_of_int n1  in
                FStar_Util.format2 " %s/%s" uu____64241 uu____64243
             in
          let maybe_label =
            match g.FStar_Tactics_Types.label with
            | "" -> ""
            | l -> Prims.op_Hat " (" (Prims.op_Hat l ")")  in
          let actual_goal =
            if ps.FStar_Tactics_Types.tac_verb_dbg
            then goal_to_string_verbose g
            else
              (let uu____64261 =
                 FStar_Syntax_Print.binders_to_string ", "
                   (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
                  in
               let uu____64264 =
                 let uu____64266 = FStar_Tactics_Types.goal_env g  in
                 tts uu____64266
                   (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                  in
               FStar_Util.format3 "%s |- %s : %s\n" uu____64261 w uu____64264)
             in
          FStar_Util.format4 "%s%s%s:\n%s\n" kind num maybe_label actual_goal
  
let (tacprint : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      let uu____64293 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____64293
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____64318 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____64318
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____64350 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____64350
  
let (comp_to_typ : FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____64360) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____64370) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (get_phi :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun g  ->
    let uu____64390 =
      let uu____64391 = FStar_Tactics_Types.goal_env g  in
      let uu____64392 = FStar_Tactics_Types.goal_type g  in
      FStar_TypeChecker_Normalize.unfold_whnf uu____64391 uu____64392  in
    FStar_Syntax_Util.un_squash uu____64390
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  -> let uu____64401 = get_phi g  in FStar_Option.isSome uu____64401 
let (print : Prims.string -> unit tac) = fun msg  -> tacprint msg; ret () 
let (debugging : unit -> Prims.bool tac) =
  fun uu____64425  ->
    bind get
      (fun ps  ->
         let uu____64433 =
           FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
             (FStar_Options.Other "Tac")
            in
         ret uu____64433)
  
let (ps_to_string :
  (Prims.string * FStar_Tactics_Types.proofstate) -> Prims.string) =
  fun uu____64448  ->
    match uu____64448 with
    | (msg,ps) ->
        let p_imp imp =
          FStar_Syntax_Print.uvar_to_string
            (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
           in
        let n_active = FStar_List.length ps.FStar_Tactics_Types.goals  in
        let n_smt = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
        let n1 = n_active + n_smt  in
        let uu____64470 =
          let uu____64474 =
            let uu____64478 =
              let uu____64480 =
                FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
              FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____64480
                msg
               in
            let uu____64483 =
              let uu____64487 =
                if
                  ps.FStar_Tactics_Types.entry_range <>
                    FStar_Range.dummyRange
                then
                  let uu____64491 =
                    FStar_Range.string_of_def_range
                      ps.FStar_Tactics_Types.entry_range
                     in
                  FStar_Util.format1 "Location: %s\n" uu____64491
                else ""  in
              let uu____64497 =
                let uu____64501 =
                  let uu____64503 =
                    FStar_TypeChecker_Env.debug
                      ps.FStar_Tactics_Types.main_context
                      (FStar_Options.Other "Imp")
                     in
                  if uu____64503
                  then
                    let uu____64508 =
                      FStar_Common.string_of_list p_imp
                        ps.FStar_Tactics_Types.all_implicits
                       in
                    FStar_Util.format1 "Imps: %s\n" uu____64508
                  else ""  in
                [uu____64501]  in
              uu____64487 :: uu____64497  in
            uu____64478 :: uu____64483  in
          let uu____64518 =
            let uu____64522 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "Goal"
                       (FStar_Pervasives_Native.Some
                          (((Prims.parse_int "1") + i), n1)) ps g)
                ps.FStar_Tactics_Types.goals
               in
            let uu____64542 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "SMT Goal"
                       (FStar_Pervasives_Native.Some
                          ((((Prims.parse_int "1") + n_active) + i), n1)) ps
                       g) ps.FStar_Tactics_Types.smt_goals
               in
            FStar_List.append uu____64522 uu____64542  in
          FStar_List.append uu____64474 uu____64518  in
        FStar_String.concat "" uu____64470
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      let uu____64572 =
        let uu____64573 = FStar_Tactics_Types.goal_env g  in
        FStar_TypeChecker_Env.all_binders uu____64573  in
      let uu____64574 =
        let uu____64579 =
          let uu____64580 = FStar_Tactics_Types.goal_env g  in
          FStar_TypeChecker_Env.dsenv uu____64580  in
        FStar_Syntax_Print.binders_to_json uu____64579  in
      FStar_All.pipe_right uu____64572 uu____64574  in
    let uu____64581 =
      let uu____64589 =
        let uu____64597 =
          let uu____64603 =
            let uu____64604 =
              let uu____64612 =
                let uu____64618 =
                  let uu____64619 =
                    let uu____64621 = FStar_Tactics_Types.goal_env g  in
                    let uu____64622 = FStar_Tactics_Types.goal_witness g  in
                    tts uu____64621 uu____64622  in
                  FStar_Util.JsonStr uu____64619  in
                ("witness", uu____64618)  in
              let uu____64625 =
                let uu____64633 =
                  let uu____64639 =
                    let uu____64640 =
                      let uu____64642 = FStar_Tactics_Types.goal_env g  in
                      let uu____64643 = FStar_Tactics_Types.goal_type g  in
                      tts uu____64642 uu____64643  in
                    FStar_Util.JsonStr uu____64640  in
                  ("type", uu____64639)  in
                [uu____64633;
                ("label", (FStar_Util.JsonStr (g.FStar_Tactics_Types.label)))]
                 in
              uu____64612 :: uu____64625  in
            FStar_Util.JsonAssoc uu____64604  in
          ("goal", uu____64603)  in
        [uu____64597]  in
      ("hyps", g_binders) :: uu____64589  in
    FStar_Util.JsonAssoc uu____64581
  
let (ps_to_json :
  (Prims.string * FStar_Tactics_Types.proofstate) -> FStar_Util.json) =
  fun uu____64697  ->
    match uu____64697 with
    | (msg,ps) ->
        let uu____64707 =
          let uu____64715 =
            let uu____64723 =
              let uu____64731 =
                let uu____64739 =
                  let uu____64745 =
                    let uu____64746 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____64746  in
                  ("goals", uu____64745)  in
                let uu____64751 =
                  let uu____64759 =
                    let uu____64765 =
                      let uu____64766 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____64766  in
                    ("smt-goals", uu____64765)  in
                  [uu____64759]  in
                uu____64739 :: uu____64751  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____64731
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____64723  in
          let uu____64800 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____64816 =
                let uu____64822 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____64822)  in
              [uu____64816]
            else []  in
          FStar_List.append uu____64715 uu____64800  in
        FStar_Util.JsonAssoc uu____64707
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____64862  ->
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
         (let uu____64893 = FStar_Tactics_Types.subst_proof_state subst1 ps
             in
          dump_proofstate uu____64893 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let traise : 'a . Prims.exn -> 'a tac =
  fun e  -> mk_tac (fun ps  -> FStar_Tactics_Result.Failed (e, ps)) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____64966 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____64966
          then dump_proofstate ps (Prims.op_Hat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed
           ((FStar_Tactics_Types.TacticFailure msg), ps))
  
let fail1 : 'Auu____64980 . Prims.string -> Prims.string -> 'Auu____64980 tac
  =
  fun msg  ->
    fun x  -> let uu____64997 = FStar_Util.format1 msg x  in fail uu____64997
  
let fail2 :
  'Auu____65008 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____65008 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        let uu____65032 = FStar_Util.format2 msg x y  in fail uu____65032
  
let fail3 :
  'Auu____65045 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____65045 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____65076 = FStar_Util.format3 msg x y z  in fail uu____65076
  
let fail4 :
  'Auu____65091 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____65091 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____65129 = FStar_Util.format4 msg x y z w  in
            fail uu____65129
  
let catch : 'a . 'a tac -> (Prims.exn,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____65164 = run t ps  in
         match uu____65164 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___802_65188 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___802_65188.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___802_65188.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___802_65188.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___802_65188.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___802_65188.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___802_65188.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___802_65188.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___802_65188.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___802_65188.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___802_65188.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___802_65188.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (uu___802_65188.FStar_Tactics_Types.local_state)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let recover : 'a . 'a tac -> (Prims.exn,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let uu____65227 = run t ps  in
         match uu____65227 with
         | FStar_Tactics_Result.Success (a,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inr a), q)
         | FStar_Tactics_Result.Failed (m,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inl m), q))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____65275 = catch t  in
    bind uu____65275
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____65302 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try
           (fun uu___828_65334  ->
              match () with
              | () -> let uu____65339 = trytac t  in run uu____65339 ps) ()
         with
         | FStar_Errors.Err (uu____65355,msg) ->
             (log ps
                (fun uu____65361  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____65367,msg,uu____65369) ->
             (log ps
                (fun uu____65374  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____65411 = run t ps  in
           match uu____65411 with
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
  fun p  -> mk_tac (fun uu____65435  -> FStar_Tactics_Result.Success ((), p)) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___863_65450 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___863_65450.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___863_65450.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___863_65450.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___863_65450.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___863_65450.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___863_65450.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___863_65450.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___863_65450.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___863_65450.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___863_65450.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___863_65450.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___863_65450.FStar_Tactics_Types.local_state)
            }))
  
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____65474 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____65474
         then
           let uu____65478 = FStar_Syntax_Print.term_to_string t1  in
           let uu____65480 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____65478
             uu____65480
         else ());
        (try
           (fun uu___871_65491  ->
              match () with
              | () ->
                  let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
                  ((let uu____65499 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____65499
                    then
                      let uu____65503 =
                        FStar_Common.string_of_option
                          (FStar_TypeChecker_Rel.guard_to_string env) res
                         in
                      let uu____65505 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____65507 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.print3
                        "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____65503
                        uu____65505 uu____65507
                    else ());
                   (match res with
                    | FStar_Pervasives_Native.None  -> ret false
                    | FStar_Pervasives_Native.Some g ->
                        let uu____65518 =
                          add_implicits g.FStar_TypeChecker_Env.implicits  in
                        bind uu____65518 (fun uu____65523  -> ret true)))) ()
         with
         | FStar_Errors.Err (uu____65533,msg) ->
             mlog
               (fun uu____65539  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____65542  -> ret false)
         | FStar_Errors.Error (uu____65545,msg,r) ->
             mlog
               (fun uu____65553  ->
                  let uu____65554 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____65554) (fun uu____65558  -> ret false))
  
let (compress_implicits : unit tac) =
  bind get
    (fun ps  ->
       let imps = ps.FStar_Tactics_Types.all_implicits  in
       let g =
         let uu___897_65572 = FStar_TypeChecker_Env.trivial_guard  in
         {
           FStar_TypeChecker_Env.guard_f =
             (uu___897_65572.FStar_TypeChecker_Env.guard_f);
           FStar_TypeChecker_Env.deferred =
             (uu___897_65572.FStar_TypeChecker_Env.deferred);
           FStar_TypeChecker_Env.univ_ineqs =
             (uu___897_65572.FStar_TypeChecker_Env.univ_ineqs);
           FStar_TypeChecker_Env.implicits = imps
         }  in
       let g1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g
          in
       let ps' =
         let uu___901_65575 = ps  in
         {
           FStar_Tactics_Types.main_context =
             (uu___901_65575.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___901_65575.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (g1.FStar_TypeChecker_Env.implicits);
           FStar_Tactics_Types.goals =
             (uu___901_65575.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___901_65575.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___901_65575.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___901_65575.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___901_65575.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___901_65575.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___901_65575.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___901_65575.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___901_65575.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___901_65575.FStar_Tactics_Types.local_state)
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
          (fun uu____65602  ->
             (let uu____65604 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____65604
              then
                (FStar_Options.push ();
                 (let uu____65609 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____65613 = __do_unify env t1 t2  in
              bind uu____65613
                (fun r  ->
                   (let uu____65624 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____65624 then FStar_Options.pop () else ());
                   ret r)))
  
let (remove_solved_goals : unit tac) =
  bind get
    (fun ps  ->
       let ps' =
         let uu___916_65638 = ps  in
         let uu____65639 =
           FStar_List.filter
             (fun g  ->
                let uu____65645 = check_goal_solved g  in
                FStar_Option.isNone uu____65645) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___916_65638.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___916_65638.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___916_65638.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____65639;
           FStar_Tactics_Types.smt_goals =
             (uu___916_65638.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___916_65638.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___916_65638.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___916_65638.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___916_65638.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___916_65638.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___916_65638.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___916_65638.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___916_65638.FStar_Tactics_Types.local_state)
         }  in
       set ps')
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____65663 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____65663 with
      | FStar_Pervasives_Native.Some uu____65668 ->
          let uu____65669 =
            let uu____65671 = goal_to_string_verbose goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____65671  in
          fail uu____65669
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____65692 = FStar_Tactics_Types.goal_env goal  in
      let uu____65693 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____65692 solution uu____65693
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____65700 =
         let uu___929_65701 = p  in
         let uu____65702 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___929_65701.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___929_65701.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___929_65701.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____65702;
           FStar_Tactics_Types.smt_goals =
             (uu___929_65701.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___929_65701.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___929_65701.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___929_65701.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___929_65701.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___929_65701.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___929_65701.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___929_65701.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___929_65701.FStar_Tactics_Types.local_state)
         }  in
       set uu____65700)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      mlog
        (fun uu____65724  ->
           let uu____65725 =
             let uu____65727 = FStar_Tactics_Types.goal_witness goal  in
             FStar_Syntax_Print.term_to_string uu____65727  in
           let uu____65728 = FStar_Syntax_Print.term_to_string solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____65725 uu____65728)
        (fun uu____65733  ->
           let uu____65734 = trysolve goal solution  in
           bind uu____65734
             (fun b  ->
                if b
                then bind __dismiss (fun uu____65746  -> remove_solved_goals)
                else
                  (let uu____65749 =
                     let uu____65751 =
                       let uu____65753 = FStar_Tactics_Types.goal_env goal
                          in
                       tts uu____65753 solution  in
                     let uu____65754 =
                       let uu____65756 = FStar_Tactics_Types.goal_env goal
                          in
                       let uu____65757 =
                         FStar_Tactics_Types.goal_witness goal  in
                       tts uu____65756 uu____65757  in
                     let uu____65758 =
                       let uu____65760 = FStar_Tactics_Types.goal_env goal
                          in
                       let uu____65761 = FStar_Tactics_Types.goal_type goal
                          in
                       tts uu____65760 uu____65761  in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____65751 uu____65754 uu____65758
                      in
                   fail uu____65749)))
  
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____65778 = set_solution goal solution  in
      bind uu____65778
        (fun uu____65782  ->
           bind __dismiss (fun uu____65784  -> remove_solved_goals))
  
let (set_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___945_65803 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___945_65803.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___945_65803.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___945_65803.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals = gs;
              FStar_Tactics_Types.smt_goals =
                (uu___945_65803.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___945_65803.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___945_65803.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___945_65803.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___945_65803.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___945_65803.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___945_65803.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___945_65803.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___945_65803.FStar_Tactics_Types.local_state)
            }))
  
let (set_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___949_65822 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___949_65822.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___949_65822.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___949_65822.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___949_65822.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals = gs;
              FStar_Tactics_Types.depth =
                (uu___949_65822.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___949_65822.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___949_65822.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___949_65822.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___949_65822.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___949_65822.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___949_65822.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___949_65822.FStar_Tactics_Types.local_state)
            }))
  
let (dismiss_all : unit tac) = set_goals [] 
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____65838 = FStar_Options.defensive ()  in
    if uu____65838
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____65848 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____65848)
         in
      let b2 =
        b1 &&
          (let uu____65852 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____65852)
         in
      let rec aux b3 e =
        let uu____65867 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____65867 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____65887 =
        (let uu____65891 = aux b2 env  in Prims.op_Negation uu____65891) &&
          (let uu____65894 = FStar_ST.op_Bang nwarn  in
           uu____65894 < (Prims.parse_int "5"))
         in
      (if uu____65887
       then
         ((let uu____65920 =
             let uu____65921 = FStar_Tactics_Types.goal_type g  in
             uu____65921.FStar_Syntax_Syntax.pos  in
           let uu____65924 =
             let uu____65930 =
               let uu____65932 = goal_to_string_verbose g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____65932
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____65930)  in
           FStar_Errors.log_issue uu____65920 uu____65924);
          (let uu____65936 =
             let uu____65938 = FStar_ST.op_Bang nwarn  in
             uu____65938 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____65936))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___971_66007 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___971_66007.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___971_66007.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___971_66007.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___971_66007.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___971_66007.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___971_66007.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___971_66007.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___971_66007.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___971_66007.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___971_66007.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___971_66007.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___971_66007.FStar_Tactics_Types.local_state)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___976_66028 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___976_66028.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___976_66028.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___976_66028.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___976_66028.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___976_66028.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___976_66028.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___976_66028.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___976_66028.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___976_66028.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___976_66028.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___976_66028.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___976_66028.FStar_Tactics_Types.local_state)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___981_66049 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___981_66049.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___981_66049.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___981_66049.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___981_66049.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___981_66049.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___981_66049.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___981_66049.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___981_66049.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___981_66049.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___981_66049.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___981_66049.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___981_66049.FStar_Tactics_Types.local_state)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___986_66070 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___986_66070.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___986_66070.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___986_66070.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___986_66070.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___986_66070.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___986_66070.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___986_66070.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___986_66070.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___986_66070.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___986_66070.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___986_66070.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___986_66070.FStar_Tactics_Types.local_state)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____66082  -> add_goals [g]) 
let (new_uvar :
  Prims.string ->
    env ->
      FStar_Reflection_Data.typ ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar) tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____66113 =
          FStar_TypeChecker_Env.new_implicit_var_aux reason
            typ.FStar_Syntax_Syntax.pos env typ
            FStar_Syntax_Syntax.Allow_untyped FStar_Pervasives_Native.None
           in
        match uu____66113 with
        | (u,ctx_uvar,g_u) ->
            let uu____66151 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____66151
              (fun uu____66160  ->
                 let uu____66161 =
                   let uu____66166 =
                     let uu____66167 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____66167  in
                   (u, uu____66166)  in
                 ret uu____66161)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____66188 = FStar_Syntax_Util.un_squash t1  in
    match uu____66188 with
    | FStar_Pervasives_Native.Some t' ->
        let t'1 = FStar_Syntax_Util.unascribe t'  in
        let uu____66200 =
          let uu____66201 = FStar_Syntax_Subst.compress t'1  in
          uu____66201.FStar_Syntax_Syntax.n  in
        (match uu____66200 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____66206 -> false)
    | uu____66208 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____66221 = FStar_Syntax_Util.un_squash t  in
    match uu____66221 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____66232 =
          let uu____66233 = FStar_Syntax_Subst.compress t'  in
          uu____66233.FStar_Syntax_Syntax.n  in
        (match uu____66232 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____66238 -> false)
    | uu____66240 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____66253  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____66265 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____66265 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____66272 = goal_to_string_verbose hd1  in
                    let uu____66274 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____66272 uu____66274);
                   ret hd1)))
  
let (tadmit_t : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____66287 =
      bind get
        (fun ps  ->
           let uu____66293 = cur_goal ()  in
           bind uu____66293
             (fun g  ->
                (let uu____66300 =
                   let uu____66301 = FStar_Tactics_Types.goal_type g  in
                   uu____66301.FStar_Syntax_Syntax.pos  in
                 let uu____66304 =
                   let uu____66310 =
                     let uu____66312 =
                       goal_to_string "" FStar_Pervasives_Native.None ps g
                        in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____66312
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____66310)  in
                 FStar_Errors.log_issue uu____66300 uu____66304);
                solve' g t))
       in
    FStar_All.pipe_left (wrap_err "tadmit_t") uu____66287
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____66335  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___1031_66346 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___1031_66346.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___1031_66346.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___1031_66346.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___1031_66346.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___1031_66346.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___1031_66346.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___1031_66346.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___1031_66346.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___1031_66346.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___1031_66346.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___1031_66346.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (uu___1031_66346.FStar_Tactics_Types.local_state)
           }  in
         let uu____66348 = set ps1  in
         bind uu____66348
           (fun uu____66353  ->
              let uu____66354 = FStar_BigInt.of_int_fs n1  in ret uu____66354))
  
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
              let uu____66392 = env.FStar_TypeChecker_Env.universe_of env phi
                 in
              FStar_Syntax_Util.mk_squash uu____66392 phi  in
            let uu____66393 = new_uvar reason env typ  in
            bind uu____66393
              (fun uu____66408  ->
                 match uu____66408 with
                 | (uu____66415,ctx_uvar) ->
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
             (fun uu____66462  ->
                let uu____66463 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____66463)
             (fun uu____66468  ->
                let e1 =
                  let uu___1049_66470 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1049_66470.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1049_66470.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1049_66470.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1049_66470.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1049_66470.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1049_66470.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1049_66470.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1049_66470.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1049_66470.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1049_66470.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1049_66470.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1049_66470.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1049_66470.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1049_66470.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1049_66470.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1049_66470.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1049_66470.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1049_66470.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1049_66470.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1049_66470.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1049_66470.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1049_66470.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1049_66470.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1049_66470.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1049_66470.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1049_66470.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1049_66470.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1049_66470.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1049_66470.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1049_66470.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1049_66470.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1049_66470.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1049_66470.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1049_66470.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1049_66470.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1049_66470.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1049_66470.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1049_66470.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1049_66470.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1049_66470.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1049_66470.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1049_66470.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___1053_66482  ->
                     match () with
                     | () ->
                         let uu____66491 =
                           FStar_TypeChecker_TcTerm.type_of_tot_term e1 t  in
                         ret uu____66491) ()
                with
                | FStar_Errors.Err (uu____66518,msg) ->
                    let uu____66522 = tts e1 t  in
                    let uu____66524 =
                      let uu____66526 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____66526
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____66522 uu____66524 msg
                | FStar_Errors.Error (uu____66536,msg,uu____66538) ->
                    let uu____66541 = tts e1 t  in
                    let uu____66543 =
                      let uu____66545 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____66545
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____66541 uu____66543 msg))
  
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
             (fun uu____66598  ->
                let uu____66599 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc_ghost(%s)\n" uu____66599)
             (fun uu____66604  ->
                let e1 =
                  let uu___1070_66606 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1070_66606.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1070_66606.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1070_66606.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1070_66606.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1070_66606.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1070_66606.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1070_66606.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1070_66606.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1070_66606.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1070_66606.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1070_66606.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1070_66606.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1070_66606.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1070_66606.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1070_66606.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1070_66606.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1070_66606.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1070_66606.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1070_66606.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1070_66606.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1070_66606.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1070_66606.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1070_66606.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1070_66606.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1070_66606.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1070_66606.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1070_66606.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1070_66606.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1070_66606.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1070_66606.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1070_66606.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1070_66606.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1070_66606.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1070_66606.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1070_66606.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1070_66606.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1070_66606.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1070_66606.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1070_66606.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1070_66606.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1070_66606.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1070_66606.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___1074_66621  ->
                     match () with
                     | () ->
                         let uu____66630 =
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e1 t
                            in
                         (match uu____66630 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____66668,msg) ->
                    let uu____66672 = tts e1 t  in
                    let uu____66674 =
                      let uu____66676 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____66676
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____66672 uu____66674 msg
                | FStar_Errors.Error (uu____66686,msg,uu____66688) ->
                    let uu____66691 = tts e1 t  in
                    let uu____66693 =
                      let uu____66695 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____66695
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____66691 uu____66693 msg))
  
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
             (fun uu____66748  ->
                let uu____66749 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____66749)
             (fun uu____66755  ->
                let e1 =
                  let uu___1095_66757 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1095_66757.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1095_66757.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1095_66757.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1095_66757.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1095_66757.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1095_66757.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1095_66757.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1095_66757.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1095_66757.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1095_66757.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1095_66757.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1095_66757.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1095_66757.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1095_66757.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1095_66757.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1095_66757.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1095_66757.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1095_66757.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1095_66757.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1095_66757.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1095_66757.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1095_66757.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1095_66757.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1095_66757.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1095_66757.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1095_66757.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1095_66757.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1095_66757.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1095_66757.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1095_66757.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1095_66757.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1095_66757.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1095_66757.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1095_66757.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1095_66757.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1095_66757.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1095_66757.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1095_66757.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1095_66757.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1095_66757.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1095_66757.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1095_66757.FStar_TypeChecker_Env.nbe)
                  }  in
                let e2 =
                  let uu___1098_66760 = e1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1098_66760.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1098_66760.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1098_66760.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1098_66760.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1098_66760.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1098_66760.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1098_66760.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1098_66760.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1098_66760.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1098_66760.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1098_66760.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1098_66760.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1098_66760.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1098_66760.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1098_66760.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1098_66760.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1098_66760.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1098_66760.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1098_66760.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1098_66760.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1098_66760.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1098_66760.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1098_66760.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1098_66760.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___1098_66760.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1098_66760.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1098_66760.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1098_66760.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1098_66760.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1098_66760.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1098_66760.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1098_66760.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1098_66760.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1098_66760.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1098_66760.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1098_66760.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1098_66760.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1098_66760.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1098_66760.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1098_66760.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1098_66760.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1098_66760.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___1102_66775  ->
                     match () with
                     | () ->
                         let uu____66784 =
                           FStar_TypeChecker_TcTerm.tc_term e2 t  in
                         (match uu____66784 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____66822,msg) ->
                    let uu____66826 = tts e2 t  in
                    let uu____66828 =
                      let uu____66830 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____66830
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____66826 uu____66828 msg
                | FStar_Errors.Error (uu____66840,msg,uu____66842) ->
                    let uu____66845 = tts e2 t  in
                    let uu____66847 =
                      let uu____66849 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____66849
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____66845 uu____66847 msg))
  
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
  fun uu____66883  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___1127_66902 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___1127_66902.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___1127_66902.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___1127_66902.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___1127_66902.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___1127_66902.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___1127_66902.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___1127_66902.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___1127_66902.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___1127_66902.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___1127_66902.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___1127_66902.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___1127_66902.FStar_Tactics_Types.local_state)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____66927 = get_guard_policy ()  in
      bind uu____66927
        (fun old_pol  ->
           let uu____66933 = set_guard_policy pol  in
           bind uu____66933
             (fun uu____66937  ->
                bind t
                  (fun r  ->
                     let uu____66941 = set_guard_policy old_pol  in
                     bind uu____66941 (fun uu____66945  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____66949 = let uu____66954 = cur_goal ()  in trytac uu____66954  in
  bind uu____66949
    (fun uu___609_66961  ->
       match uu___609_66961 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____66967 = FStar_Options.peek ()  in ret uu____66967)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        mlog
          (fun uu____66992  ->
             let uu____66993 = FStar_TypeChecker_Rel.guard_to_string e g  in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason
               uu____66993)
          (fun uu____66998  ->
             let uu____66999 =
               add_implicits g.FStar_TypeChecker_Env.implicits  in
             bind uu____66999
               (fun uu____67003  ->
                  bind getopts
                    (fun opts  ->
                       let uu____67007 =
                         let uu____67008 =
                           FStar_TypeChecker_Rel.simplify_guard e g  in
                         uu____67008.FStar_TypeChecker_Env.guard_f  in
                       match uu____67007 with
                       | FStar_TypeChecker_Common.Trivial  -> ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____67012 = istrivial e f  in
                           if uu____67012
                           then ret ()
                           else
                             bind get
                               (fun ps  ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop  ->
                                      ((let uu____67025 =
                                          let uu____67031 =
                                            let uu____67033 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g
                                               in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____67033
                                             in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____67031)
                                           in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____67025);
                                       ret ())
                                  | FStar_Tactics_Types.Goal  ->
                                      mlog
                                        (fun uu____67039  ->
                                           let uu____67040 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____67040)
                                        (fun uu____67045  ->
                                           let uu____67046 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____67046
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___1156_67054 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___1156_67054.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___1156_67054.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___1156_67054.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___1156_67054.FStar_Tactics_Types.label)
                                                  }  in
                                                push_goals [goal1]))
                                  | FStar_Tactics_Types.SMT  ->
                                      mlog
                                        (fun uu____67058  ->
                                           let uu____67059 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____67059)
                                        (fun uu____67064  ->
                                           let uu____67065 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____67065
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___1163_67073 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___1163_67073.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___1163_67073.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___1163_67073.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___1163_67073.FStar_Tactics_Types.label)
                                                  }  in
                                                push_smt_goals [goal1]))
                                  | FStar_Tactics_Types.Force  ->
                                      mlog
                                        (fun uu____67077  ->
                                           let uu____67078 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____67078)
                                        (fun uu____67082  ->
                                           try
                                             (fun uu___1170_67087  ->
                                                match () with
                                                | () ->
                                                    let uu____67090 =
                                                      let uu____67092 =
                                                        let uu____67094 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____67094
                                                         in
                                                      Prims.op_Negation
                                                        uu____67092
                                                       in
                                                    if uu____67090
                                                    then
                                                      mlog
                                                        (fun uu____67101  ->
                                                           let uu____67102 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g
                                                              in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____67102)
                                                        (fun uu____67106  ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else ret ()) ()
                                           with
                                           | uu___1169_67111 ->
                                               mlog
                                                 (fun uu____67116  ->
                                                    let uu____67117 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g
                                                       in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____67117)
                                                 (fun uu____67121  ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____67133 =
      let uu____67136 = cur_goal ()  in
      bind uu____67136
        (fun goal  ->
           let uu____67142 =
             let uu____67151 = FStar_Tactics_Types.goal_env goal  in
             __tc_lax uu____67151 t  in
           bind uu____67142
             (fun uu____67162  ->
                match uu____67162 with
                | (uu____67171,typ,uu____67173) -> ret typ))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____67133
  
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
            let uu____67213 = mk_irrelevant_goal reason env phi opts label1
               in
            bind uu____67213 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____67225  ->
    let uu____67228 = cur_goal ()  in
    bind uu____67228
      (fun goal  ->
         let uu____67234 =
           let uu____67236 = FStar_Tactics_Types.goal_env goal  in
           let uu____67237 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____67236 uu____67237  in
         if uu____67234
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____67243 =
              let uu____67245 = FStar_Tactics_Types.goal_env goal  in
              let uu____67246 = FStar_Tactics_Types.goal_type goal  in
              tts uu____67245 uu____67246  in
            fail1 "Not a trivial goal: %s" uu____67243))
  
let divide : 'a 'b . FStar_BigInt.t -> 'a tac -> 'b tac -> ('a * 'b) tac =
  fun n1  ->
    fun l  ->
      fun r  ->
        bind get
          (fun p  ->
             let uu____67297 =
               try
                 (fun uu___1226_67320  ->
                    match () with
                    | () ->
                        let uu____67331 =
                          let uu____67340 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____67340
                            p.FStar_Tactics_Types.goals
                           in
                        ret uu____67331) ()
               with | uu___1225_67351 -> fail "divide: not enough goals"  in
             bind uu____67297
               (fun uu____67388  ->
                  match uu____67388 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___1208_67414 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___1208_67414.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___1208_67414.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___1208_67414.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___1208_67414.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___1208_67414.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___1208_67414.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___1208_67414.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___1208_67414.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___1208_67414.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___1208_67414.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___1208_67414.FStar_Tactics_Types.local_state)
                        }  in
                      let uu____67415 = set lp  in
                      bind uu____67415
                        (fun uu____67423  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___1214_67439 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___1214_67439.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___1214_67439.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___1214_67439.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___1214_67439.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___1214_67439.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___1214_67439.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___1214_67439.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___1214_67439.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___1214_67439.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___1214_67439.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___1214_67439.FStar_Tactics_Types.local_state)
                                       }  in
                                     let uu____67440 = set rp  in
                                     bind uu____67440
                                       (fun uu____67448  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___1220_67464 =
                                                        rp'  in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___1220_67464.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___1220_67464.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___1220_67464.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___1220_67464.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___1220_67464.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___1220_67464.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___1220_67464.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___1220_67464.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___1220_67464.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___1220_67464.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___1220_67464.FStar_Tactics_Types.local_state)
                                                      }  in
                                                    let uu____67465 = set p'
                                                       in
                                                    bind uu____67465
                                                      (fun uu____67473  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____67479 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____67501 = divide FStar_BigInt.one f idtac  in
    bind uu____67501
      (fun uu____67514  -> match uu____67514 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____67552::uu____67553 ->
             let uu____67556 =
               let uu____67565 = map tau  in
               divide FStar_BigInt.one tau uu____67565  in
             bind uu____67556
               (fun uu____67583  ->
                  match uu____67583 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____67625 =
        bind t1
          (fun uu____67630  ->
             let uu____67631 = map t2  in
             bind uu____67631 (fun uu____67639  -> ret ()))
         in
      focus uu____67625
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____67649  ->
    let uu____67652 =
      let uu____67655 = cur_goal ()  in
      bind uu____67655
        (fun goal  ->
           let uu____67664 =
             let uu____67671 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____67671  in
           match uu____67664 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____67680 =
                 let uu____67682 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____67682  in
               if uu____67680
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____67691 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____67691 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____67705 = new_uvar "intro" env' typ'  in
                  bind uu____67705
                    (fun uu____67722  ->
                       match uu____67722 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c))
                              in
                           let uu____67746 = set_solution goal sol  in
                           bind uu____67746
                             (fun uu____67752  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                    goal.FStar_Tactics_Types.label
                                   in
                                let uu____67754 =
                                  let uu____67757 = bnorm_goal g  in
                                  replace_cur uu____67757  in
                                bind uu____67754 (fun uu____67759  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____67764 =
                 let uu____67766 = FStar_Tactics_Types.goal_env goal  in
                 let uu____67767 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____67766 uu____67767  in
               fail1 "goal is not an arrow (%s)" uu____67764)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____67652
  
let (intro_rec :
  unit -> (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder) tac) =
  fun uu____67785  ->
    let uu____67792 = cur_goal ()  in
    bind uu____67792
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____67811 =
            let uu____67818 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____67818  in
          match uu____67811 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____67831 =
                let uu____67833 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____67833  in
              if uu____67831
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____67850 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____67850
                    in
                 let bs =
                   let uu____67861 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____67861; b]  in
                 let env' =
                   let uu____67887 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____67887 bs  in
                 let uu____67888 =
                   let uu____67895 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____67895  in
                 bind uu____67888
                   (fun uu____67915  ->
                      match uu____67915 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____67929 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____67932 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____67929
                              FStar_Parser_Const.effect_Tot_lid uu____67932
                              [] FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____67950 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____67950 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____67972 =
                                   let uu____67973 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____67973.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____67972
                                  in
                               let uu____67989 = set_solution goal tm  in
                               bind uu____67989
                                 (fun uu____67998  ->
                                    let uu____67999 =
                                      let uu____68002 =
                                        bnorm_goal
                                          (let uu___1291_68005 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___1291_68005.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___1291_68005.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___1291_68005.FStar_Tactics_Types.is_guard);
                                             FStar_Tactics_Types.label =
                                               (uu___1291_68005.FStar_Tactics_Types.label)
                                           })
                                         in
                                      replace_cur uu____68002  in
                                    bind uu____67999
                                      (fun uu____68012  ->
                                         let uu____68013 =
                                           let uu____68018 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____68018, b)  in
                                         ret uu____68013)))))
          | FStar_Pervasives_Native.None  ->
              let uu____68027 =
                let uu____68029 = FStar_Tactics_Types.goal_env goal  in
                let uu____68030 = FStar_Tactics_Types.goal_type goal  in
                tts uu____68029 uu____68030  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____68027))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____68050 = cur_goal ()  in
    bind uu____68050
      (fun goal  ->
         mlog
           (fun uu____68057  ->
              let uu____68058 =
                let uu____68060 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____68060  in
              FStar_Util.print1 "norm: witness = %s\n" uu____68058)
           (fun uu____68066  ->
              let steps =
                let uu____68070 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____68070
                 in
              let t =
                let uu____68074 = FStar_Tactics_Types.goal_env goal  in
                let uu____68075 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____68074 uu____68075  in
              let uu____68076 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____68076))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____68101 =
          bind get
            (fun ps  ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
                 | g::uu____68109 -> g.FStar_Tactics_Types.opts
                 | uu____68112 -> FStar_Options.peek ()  in
               mlog
                 (fun uu____68117  ->
                    let uu____68118 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____68118)
                 (fun uu____68123  ->
                    let uu____68124 = __tc_lax e t  in
                    bind uu____68124
                      (fun uu____68145  ->
                         match uu____68145 with
                         | (t1,uu____68155,uu____68156) ->
                             let steps =
                               let uu____68160 =
                                 FStar_TypeChecker_Normalize.tr_norm_steps s
                                  in
                               FStar_List.append
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu____68160
                                in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1
                                in
                             mlog
                               (fun uu____68166  ->
                                  let uu____68167 =
                                    FStar_Syntax_Print.term_to_string t2  in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____68167)
                               (fun uu____68171  -> ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____68101
  
let (refine_intro : unit -> unit tac) =
  fun uu____68184  ->
    let uu____68187 =
      let uu____68190 = cur_goal ()  in
      bind uu____68190
        (fun g  ->
           let uu____68197 =
             let uu____68208 = FStar_Tactics_Types.goal_env g  in
             let uu____68209 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____68208
               uu____68209
              in
           match uu____68197 with
           | (uu____68212,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____68238 =
                 let uu____68243 =
                   let uu____68248 =
                     let uu____68249 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____68249]  in
                   FStar_Syntax_Subst.open_term uu____68248 phi  in
                 match uu____68243 with
                 | (bvs,phi1) ->
                     let uu____68274 =
                       let uu____68275 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____68275  in
                     (uu____68274, phi1)
                  in
               (match uu____68238 with
                | (bv1,phi1) ->
                    let uu____68294 =
                      let uu____68297 = FStar_Tactics_Types.goal_env g  in
                      let uu____68298 =
                        let uu____68299 =
                          let uu____68302 =
                            let uu____68303 =
                              let uu____68310 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____68310)  in
                            FStar_Syntax_Syntax.NT uu____68303  in
                          [uu____68302]  in
                        FStar_Syntax_Subst.subst uu____68299 phi1  in
                      mk_irrelevant_goal "refine_intro refinement"
                        uu____68297 uu____68298 g.FStar_Tactics_Types.opts
                        g.FStar_Tactics_Types.label
                       in
                    bind uu____68294
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____68319  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____68187
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____68342 = cur_goal ()  in
      bind uu____68342
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____68351 = FStar_Tactics_Types.goal_env goal  in
               let uu____68352 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____68351 uu____68352
             else FStar_Tactics_Types.goal_env goal  in
           let uu____68355 = __tc env t  in
           bind uu____68355
             (fun uu____68374  ->
                match uu____68374 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____68389  ->
                         let uu____68390 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____68392 =
                           let uu____68394 =
                             FStar_Tactics_Types.goal_env goal  in
                           FStar_TypeChecker_Rel.guard_to_string uu____68394
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____68390 uu____68392)
                      (fun uu____68398  ->
                         let uu____68399 =
                           let uu____68402 =
                             FStar_Tactics_Types.goal_env goal  in
                           proc_guard "__exact typing" uu____68402 guard  in
                         bind uu____68399
                           (fun uu____68405  ->
                              mlog
                                (fun uu____68409  ->
                                   let uu____68410 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____68412 =
                                     let uu____68414 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____68414
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____68410 uu____68412)
                                (fun uu____68418  ->
                                   let uu____68419 =
                                     let uu____68423 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____68424 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____68423 typ uu____68424  in
                                   bind uu____68419
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____68434 =
                                             let uu____68436 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____68436 t1  in
                                           let uu____68437 =
                                             let uu____68439 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____68439 typ  in
                                           let uu____68440 =
                                             let uu____68442 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____68443 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____68442 uu____68443  in
                                           let uu____68444 =
                                             let uu____68446 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____68447 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____68446 uu____68447  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____68434 uu____68437
                                             uu____68440 uu____68444)))))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun try_refine  ->
    fun set_expected_typ1  ->
      fun tm  ->
        let uu____68473 =
          mlog
            (fun uu____68478  ->
               let uu____68479 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____68479)
            (fun uu____68484  ->
               let uu____68485 =
                 let uu____68492 = __exact_now set_expected_typ1 tm  in
                 catch uu____68492  in
               bind uu____68485
                 (fun uu___611_68501  ->
                    match uu___611_68501 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        traise e
                    | FStar_Util.Inl e ->
                        mlog
                          (fun uu____68512  ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____68516  ->
                             let uu____68517 =
                               let uu____68524 =
                                 let uu____68527 =
                                   norm [FStar_Syntax_Embeddings.Delta]  in
                                 bind uu____68527
                                   (fun uu____68532  ->
                                      let uu____68533 = refine_intro ()  in
                                      bind uu____68533
                                        (fun uu____68537  ->
                                           __exact_now set_expected_typ1 tm))
                                  in
                               catch uu____68524  in
                             bind uu____68517
                               (fun uu___610_68544  ->
                                  match uu___610_68544 with
                                  | FStar_Util.Inr r ->
                                      mlog
                                        (fun uu____68553  ->
                                           FStar_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu____68556  -> ret ())
                                  | FStar_Util.Inl uu____68557 ->
                                      mlog
                                        (fun uu____68559  ->
                                           FStar_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu____68562  -> traise e)))))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____68473
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____68614 = f x  in
          bind uu____68614
            (fun y  ->
               let uu____68622 = mapM f xs  in
               bind uu____68622 (fun ys  -> ret (y :: ys)))
  
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
          let uu____68694 = do_unify e ty1 ty2  in
          bind uu____68694
            (fun uu___612_68708  ->
               if uu___612_68708
               then ret acc
               else
                 (let uu____68728 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____68728 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____68749 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____68751 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____68749
                        uu____68751
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____68768 =
                        let uu____68770 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____68770  in
                      if uu____68768
                      then fail "Codomain is effectful"
                      else
                        (let uu____68794 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____68794
                           (fun uu____68821  ->
                              match uu____68821 with
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
      let uu____68911 =
        mlog
          (fun uu____68916  ->
             let uu____68917 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_apply: tm = %s\n" uu____68917)
          (fun uu____68922  ->
             let uu____68923 = cur_goal ()  in
             bind uu____68923
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____68931 = __tc e tm  in
                  bind uu____68931
                    (fun uu____68952  ->
                       match uu____68952 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____68965 =
                             let uu____68976 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____68976  in
                           bind uu____68965
                             (fun uvs  ->
                                let fix_qual q =
                                  match q with
                                  | FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Meta uu____69014)
                                      ->
                                      FStar_Pervasives_Native.Some
                                        (FStar_Syntax_Syntax.Implicit false)
                                  | uu____69018 -> q  in
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____69041  ->
                                       fun w  ->
                                         match uu____69041 with
                                         | (uvt,q,uu____69059) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, (fix_qual q))]) uvs tm1
                                   in
                                let uvset =
                                  let uu____69091 =
                                    FStar_Syntax_Free.new_uv_set ()  in
                                  FStar_List.fold_right
                                    (fun uu____69108  ->
                                       fun s  ->
                                         match uu____69108 with
                                         | (uu____69120,uu____69121,uv) ->
                                             let uu____69123 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                in
                                             FStar_Util.set_union s
                                               uu____69123) uvs uu____69091
                                   in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset  in
                                let uu____69133 = solve' goal w  in
                                bind uu____69133
                                  (fun uu____69138  ->
                                     let uu____69139 =
                                       mapM
                                         (fun uu____69156  ->
                                            match uu____69156 with
                                            | (uvt,q,uv) ->
                                                let uu____69168 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                   in
                                                (match uu____69168 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____69173 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____69174 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv)
                                                        in
                                                     if uu____69174
                                                     then ret ()
                                                     else
                                                       (let uu____69181 =
                                                          let uu____69184 =
                                                            bnorm_goal
                                                              (let uu___1452_69187
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___1452_69187.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___1452_69187.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false;
                                                                 FStar_Tactics_Types.label
                                                                   =
                                                                   (uu___1452_69187.FStar_Tactics_Types.label)
                                                               })
                                                             in
                                                          [uu____69184]  in
                                                        add_goals uu____69181)))
                                         uvs
                                        in
                                     bind uu____69139
                                       (fun uu____69192  ->
                                          proc_guard "apply guard" e guard))))))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____68911
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____69220 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____69220
    then
      let uu____69229 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____69244 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____69297 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____69229 with
      | (pre,post) ->
          let post1 =
            let uu____69330 =
              let uu____69341 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____69341]  in
            FStar_Syntax_Util.mk_app post uu____69330  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____69372 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____69372
       then
         let uu____69381 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____69381
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
            let uu____69460 = f x e  in
            bind uu____69460 (fun e'  -> fold_left f e' xs1)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____69475 =
      let uu____69478 =
        bind get
          (fun ps  ->
             mlog
               (fun uu____69485  ->
                  let uu____69486 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____69486)
               (fun uu____69492  ->
                  let is_unit_t t =
                    let uu____69500 =
                      let uu____69501 = FStar_Syntax_Subst.compress t  in
                      uu____69501.FStar_Syntax_Syntax.n  in
                    match uu____69500 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____69507 -> false  in
                  let uu____69509 = cur_goal ()  in
                  bind uu____69509
                    (fun goal  ->
                       let uu____69515 =
                         let uu____69524 = FStar_Tactics_Types.goal_env goal
                            in
                         __tc uu____69524 tm  in
                       bind uu____69515
                         (fun uu____69539  ->
                            match uu____69539 with
                            | (tm1,t,guard) ->
                                let uu____69551 =
                                  FStar_Syntax_Util.arrow_formals_comp t  in
                                (match uu____69551 with
                                 | (bs,comp) ->
                                     let uu____69584 = lemma_or_sq comp  in
                                     (match uu____69584 with
                                      | FStar_Pervasives_Native.None  ->
                                          fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre,post) ->
                                          let uu____69604 =
                                            fold_left
                                              (fun uu____69666  ->
                                                 fun uu____69667  ->
                                                   match (uu____69666,
                                                           uu____69667)
                                                   with
                                                   | ((b,aq),(uvs,imps,subst1))
                                                       ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst1
                                                           b.FStar_Syntax_Syntax.sort
                                                          in
                                                       let uu____69818 =
                                                         is_unit_t b_t  in
                                                       if uu____69818
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
                                                         (let uu____69941 =
                                                            let uu____69948 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            new_uvar
                                                              "apply_lemma"
                                                              uu____69948 b_t
                                                             in
                                                          bind uu____69941
                                                            (fun uu____69979 
                                                               ->
                                                               match uu____69979
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
                                          bind uu____69604
                                            (fun uu____70165  ->
                                               match uu____70165 with
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
                                                   let uu____70253 =
                                                     let uu____70257 =
                                                       FStar_Tactics_Types.goal_env
                                                         goal
                                                        in
                                                     let uu____70258 =
                                                       FStar_Syntax_Util.mk_squash
                                                         FStar_Syntax_Syntax.U_zero
                                                         post1
                                                        in
                                                     let uu____70259 =
                                                       FStar_Tactics_Types.goal_type
                                                         goal
                                                        in
                                                     do_unify uu____70257
                                                       uu____70258
                                                       uu____70259
                                                      in
                                                   bind uu____70253
                                                     (fun b  ->
                                                        if
                                                          Prims.op_Negation b
                                                        then
                                                          let uu____70270 =
                                                            let uu____70272 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            tts uu____70272
                                                              tm1
                                                             in
                                                          let uu____70273 =
                                                            let uu____70275 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            let uu____70276 =
                                                              FStar_Syntax_Util.mk_squash
                                                                FStar_Syntax_Syntax.U_zero
                                                                post1
                                                               in
                                                            tts uu____70275
                                                              uu____70276
                                                             in
                                                          let uu____70277 =
                                                            let uu____70279 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            let uu____70280 =
                                                              FStar_Tactics_Types.goal_type
                                                                goal
                                                               in
                                                            tts uu____70279
                                                              uu____70280
                                                             in
                                                          fail3
                                                            "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                            uu____70270
                                                            uu____70273
                                                            uu____70277
                                                        else
                                                          (let uu____70284 =
                                                             solve' goal
                                                               FStar_Syntax_Util.exp_unit
                                                              in
                                                           bind uu____70284
                                                             (fun uu____70292
                                                                 ->
                                                                let is_free_uvar
                                                                  uv t1 =
                                                                  let free_uvars
                                                                    =
                                                                    let uu____70318
                                                                    =
                                                                    let uu____70321
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____70321
                                                                     in
                                                                    FStar_List.map
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____70318
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
                                                                    let uu____70357
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____70357)
                                                                    goals
                                                                   in
                                                                let checkone
                                                                  t1 goals =
                                                                  let uu____70374
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                  match uu____70374
                                                                  with
                                                                  | (hd1,uu____70393)
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____70420)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____70437
                                                                    -> false)
                                                                   in
                                                                let uu____70439
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
                                                                    let uu____70482
                                                                    = imp  in
                                                                    match uu____70482
                                                                    with
                                                                    | 
                                                                    (term,ctx_uvar)
                                                                    ->
                                                                    let uu____70493
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____70493
                                                                    with
                                                                    | 
                                                                    (hd1,uu____70515)
                                                                    ->
                                                                    let uu____70540
                                                                    =
                                                                    let uu____70541
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____70541.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____70540
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____70549)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___1562_70569
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___1562_70569.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___1562_70569.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___1562_70569.FStar_Tactics_Types.is_guard);
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___1562_70569.FStar_Tactics_Types.label)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____70572
                                                                    ->
                                                                    mlog
                                                                    (fun
                                                                    uu____70578
                                                                     ->
                                                                    let uu____70579
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                                                     in
                                                                    let uu____70581
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____70579
                                                                    uu____70581)
                                                                    (fun
                                                                    uu____70588
                                                                     ->
                                                                    let env =
                                                                    let uu___1567_70590
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___1567_70590.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1567_70590.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1567_70590.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___1567_70590.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1567_70590.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1567_70590.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1567_70590.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1567_70590.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___1567_70590.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___1567_70590.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___1567_70590.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1567_70590.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1567_70590.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1567_70590.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1567_70590.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1567_70590.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1567_70590.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1567_70590.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___1567_70590.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___1567_70590.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___1567_70590.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1567_70590.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1567_70590.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1567_70590.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1567_70590.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1567_70590.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1567_70590.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1567_70590.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1567_70590.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1567_70590.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1567_70590.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1567_70590.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1567_70590.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1567_70590.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___1567_70590.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1567_70590.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1567_70590.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___1567_70590.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1567_70590.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1567_70590.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1567_70590.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1567_70590.FStar_TypeChecker_Env.nbe)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let uu____70593
                                                                    =
                                                                    let uu____70596
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____70600
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
                                                                    let uu____70602
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____70600
                                                                    uu____70602
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____70608
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    uu____70596
                                                                    uu____70608
                                                                    g_typ  in
                                                                    bind
                                                                    uu____70593
                                                                    (fun
                                                                    uu____70612
                                                                     ->
                                                                    ret []))))))
                                                                   in
                                                                bind
                                                                  uu____70439
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
                                                                    let uu____70676
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____70676
                                                                    then
                                                                    let uu____70681
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____70681
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
                                                                    let uu____70696
                                                                    =
                                                                    let uu____70698
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____70698
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____70696)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____70699
                                                                    =
                                                                    let uu____70702
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____70702
                                                                    guard  in
                                                                    bind
                                                                    uu____70699
                                                                    (fun
                                                                    uu____70706
                                                                     ->
                                                                    let uu____70707
                                                                    =
                                                                    let uu____70710
                                                                    =
                                                                    let uu____70712
                                                                    =
                                                                    let uu____70714
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____70715
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____70714
                                                                    uu____70715
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____70712
                                                                     in
                                                                    if
                                                                    uu____70710
                                                                    then
                                                                    let uu____70719
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____70719
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    goal.FStar_Tactics_Types.label
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____70707
                                                                    (fun
                                                                    uu____70724
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2)))))))))))))
         in
      focus uu____69478  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____69475
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____70748 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____70748 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____70758::(e1,uu____70760)::(e2,uu____70762)::[])) when
        (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) ||
          (FStar_Ident.lid_equals l FStar_Parser_Const.c_eq2_lid)
        -> FStar_Pervasives_Native.Some (e1, e2)
    | uu____70823 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____70848 = destruct_eq' typ  in
    match uu____70848 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____70878 = FStar_Syntax_Util.un_squash typ  in
        (match uu____70878 with
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
        let uu____70947 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____70947 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', bv', [])
            else
              (let uu____71005 = aux e'  in
               FStar_Util.map_opt uu____71005
                 (fun uu____71036  ->
                    match uu____71036 with
                    | (e'',bv,bvs) -> (e'', bv, (bv' :: bvs))))
         in
      let uu____71062 = aux e  in
      FStar_Util.map_opt uu____71062
        (fun uu____71093  ->
           match uu____71093 with
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
          let uu____71167 =
            let uu____71178 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____71178  in
          FStar_Util.map_opt uu____71167
            (fun uu____71196  ->
               match uu____71196 with
               | (e0,b11,bvs) ->
                   let s1 bv =
                     let uu___1640_71218 = bv  in
                     let uu____71219 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___1640_71218.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___1640_71218.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____71219
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___1644_71227 =
                       g.FStar_Tactics_Types.goal_ctx_uvar  in
                     let uu____71228 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____71237 =
                       let uu____71240 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____71240  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___1644_71227.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____71228;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____71237;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___1644_71227.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___1644_71227.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___1644_71227.FStar_Syntax_Syntax.ctx_uvar_range);
                       FStar_Syntax_Syntax.ctx_uvar_meta =
                         (uu___1644_71227.FStar_Syntax_Syntax.ctx_uvar_meta)
                     }  in
                   let uu___1647_71241 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1647_71241.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___1647_71241.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___1647_71241.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1647_71241.FStar_Tactics_Types.label)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____71252 =
      let uu____71255 = cur_goal ()  in
      bind uu____71255
        (fun goal  ->
           let uu____71263 = h  in
           match uu____71263 with
           | (bv,uu____71267) ->
               mlog
                 (fun uu____71275  ->
                    let uu____71276 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____71278 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____71276
                      uu____71278)
                 (fun uu____71283  ->
                    let uu____71284 =
                      let uu____71295 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____71295  in
                    match uu____71284 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                        let uu____71322 =
                          destruct_eq bv1.FStar_Syntax_Syntax.sort  in
                        (match uu____71322 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____71337 =
                               let uu____71338 =
                                 FStar_Syntax_Subst.compress x  in
                               uu____71338.FStar_Syntax_Syntax.n  in
                             (match uu____71337 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv2 =
                                    let uu___1670_71355 = bv2  in
                                    let uu____71356 =
                                      FStar_Syntax_Subst.subst s
                                        bv2.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1670_71355.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1670_71355.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____71356
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv1 :: bvs1)  in
                                  let new_goal =
                                    let uu___1674_71364 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____71365 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____71374 =
                                      let uu____71377 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____71377
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___1674_71364.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____71365;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____71374;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___1674_71364.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___1674_71364.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___1674_71364.FStar_Syntax_Syntax.ctx_uvar_range);
                                      FStar_Syntax_Syntax.ctx_uvar_meta =
                                        (uu___1674_71364.FStar_Syntax_Syntax.ctx_uvar_meta)
                                    }  in
                                  replace_cur
                                    (let uu___1677_71380 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___1677_71380.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___1677_71380.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___1677_71380.FStar_Tactics_Types.is_guard);
                                       FStar_Tactics_Types.label =
                                         (uu___1677_71380.FStar_Tactics_Types.label)
                                     })
                              | uu____71381 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____71383 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____71252
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____71413 =
        let uu____71416 = cur_goal ()  in
        bind uu____71416
          (fun goal  ->
             let uu____71427 = b  in
             match uu____71427 with
             | (bv,uu____71431) ->
                 let bv' =
                   let uu____71437 =
                     let uu___1688_71438 = bv  in
                     let uu____71439 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____71439;
                       FStar_Syntax_Syntax.index =
                         (uu___1688_71438.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___1688_71438.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____71437  in
                 let s1 =
                   let uu____71444 =
                     let uu____71445 =
                       let uu____71452 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____71452)  in
                     FStar_Syntax_Syntax.NT uu____71445  in
                   [uu____71444]  in
                 let uu____71457 = subst_goal bv bv' s1 goal  in
                 (match uu____71457 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____71413
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____71479 =
      let uu____71482 = cur_goal ()  in
      bind uu____71482
        (fun goal  ->
           let uu____71491 = b  in
           match uu____71491 with
           | (bv,uu____71495) ->
               let uu____71500 =
                 let uu____71511 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____71511  in
               (match uu____71500 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                    let uu____71538 = FStar_Syntax_Util.type_u ()  in
                    (match uu____71538 with
                     | (ty,u) ->
                         let uu____71547 = new_uvar "binder_retype" e0 ty  in
                         bind uu____71547
                           (fun uu____71566  ->
                              match uu____71566 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___1712_71576 = bv1  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1712_71576.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1712_71576.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____71580 =
                                      let uu____71581 =
                                        let uu____71588 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv1, uu____71588)  in
                                      FStar_Syntax_Syntax.NT uu____71581  in
                                    [uu____71580]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___1717_71600 = b1  in
                                         let uu____71601 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___1717_71600.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___1717_71600.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____71601
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____71608  ->
                                       let new_goal =
                                         let uu____71610 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____71611 =
                                           let uu____71612 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____71612
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____71610 uu____71611
                                          in
                                       let uu____71613 = add_goals [new_goal]
                                          in
                                       bind uu____71613
                                         (fun uu____71618  ->
                                            let uu____71619 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv1.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____71619
                                              goal.FStar_Tactics_Types.opts
                                              goal.FStar_Tactics_Types.label))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____71479
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____71645 =
        let uu____71648 = cur_goal ()  in
        bind uu____71648
          (fun goal  ->
             let uu____71657 = b  in
             match uu____71657 with
             | (bv,uu____71661) ->
                 let uu____71666 =
                   let uu____71677 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____71677  in
                 (match uu____71666 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                      let steps =
                        let uu____71707 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____71707
                         in
                      let sort' =
                        normalize steps e0 bv1.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___1738_71712 = bv1  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___1738_71712.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___1738_71712.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____71714 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____71714))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____71645
  
let (revert : unit -> unit tac) =
  fun uu____71727  ->
    let uu____71730 = cur_goal ()  in
    bind uu____71730
      (fun goal  ->
         let uu____71736 =
           let uu____71743 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____71743  in
         match uu____71736 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____71760 =
                 let uu____71763 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____71763  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____71760
                in
             let uu____71778 = new_uvar "revert" env' typ'  in
             bind uu____71778
               (fun uu____71794  ->
                  match uu____71794 with
                  | (r,u_r) ->
                      let uu____71803 =
                        let uu____71806 =
                          let uu____71807 =
                            let uu____71808 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____71808.FStar_Syntax_Syntax.pos  in
                          let uu____71811 =
                            let uu____71816 =
                              let uu____71817 =
                                let uu____71826 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____71826  in
                              [uu____71817]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____71816  in
                          uu____71811 FStar_Pervasives_Native.None
                            uu____71807
                           in
                        set_solution goal uu____71806  in
                      bind uu____71803
                        (fun uu____71845  ->
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
      let uu____71859 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____71859
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____71875 = cur_goal ()  in
    bind uu____71875
      (fun goal  ->
         mlog
           (fun uu____71883  ->
              let uu____71884 = FStar_Syntax_Print.binder_to_string b  in
              let uu____71886 =
                let uu____71888 =
                  let uu____71890 =
                    let uu____71899 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____71899  in
                  FStar_All.pipe_right uu____71890 FStar_List.length  in
                FStar_All.pipe_right uu____71888 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____71884 uu____71886)
           (fun uu____71920  ->
              let uu____71921 =
                let uu____71932 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____71932  in
              match uu____71921 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bv1,bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____71977 =
                          free_in bv1 bv'.FStar_Syntax_Syntax.sort  in
                        if uu____71977
                        then
                          let uu____71982 =
                            let uu____71984 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____71984
                             in
                          fail uu____71982
                        else check1 bvs2
                     in
                  let uu____71989 =
                    let uu____71991 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv1 uu____71991  in
                  if uu____71989
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____71998 = check1 bvs  in
                     bind uu____71998
                       (fun uu____72004  ->
                          let env' = push_bvs e' bvs  in
                          let uu____72006 =
                            let uu____72013 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____72013  in
                          bind uu____72006
                            (fun uu____72023  ->
                               match uu____72023 with
                               | (ut,uvar_ut) ->
                                   let uu____72032 = set_solution goal ut  in
                                   bind uu____72032
                                     (fun uu____72037  ->
                                        let uu____72038 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                            goal.FStar_Tactics_Types.label
                                           in
                                        replace_cur uu____72038))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____72046  ->
    let uu____72049 = cur_goal ()  in
    bind uu____72049
      (fun goal  ->
         let uu____72055 =
           let uu____72062 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____72062  in
         match uu____72055 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____72071) ->
             let uu____72076 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____72076)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____72089 = cur_goal ()  in
    bind uu____72089
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____72099 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____72099  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____72102  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____72115 = cur_goal ()  in
    bind uu____72115
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____72125 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____72125  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____72128  -> add_goals [g']))
  
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
            let uu____72169 = FStar_Syntax_Subst.compress t  in
            uu____72169.FStar_Syntax_Syntax.n  in
          let uu____72172 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___1922_72179 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___1922_72179.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___1922_72179.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____72172
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____72196 =
                   let uu____72197 = FStar_Syntax_Subst.compress t1  in
                   uu____72197.FStar_Syntax_Syntax.n  in
                 match uu____72196 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____72228 = ff hd1  in
                     bind uu____72228
                       (fun hd2  ->
                          let fa uu____72254 =
                            match uu____72254 with
                            | (a,q) ->
                                let uu____72275 = ff a  in
                                bind uu____72275 (fun a1  -> ret (a1, q))
                             in
                          let uu____72294 = mapM fa args  in
                          bind uu____72294
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____72376 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____72376 with
                      | (bs1,t') ->
                          let uu____72385 =
                            let uu____72388 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____72388 t'  in
                          bind uu____72385
                            (fun t''  ->
                               let uu____72392 =
                                 let uu____72393 =
                                   let uu____72412 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____72421 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____72412, uu____72421, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____72393  in
                               ret uu____72392))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____72496 = ff hd1  in
                     bind uu____72496
                       (fun hd2  ->
                          let ffb br =
                            let uu____72511 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____72511 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____72543 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____72543  in
                                let uu____72544 = ff1 e  in
                                bind uu____72544
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____72559 = mapM ffb brs  in
                          bind uu____72559
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____72603;
                          FStar_Syntax_Syntax.lbtyp = uu____72604;
                          FStar_Syntax_Syntax.lbeff = uu____72605;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____72607;
                          FStar_Syntax_Syntax.lbpos = uu____72608;_}::[]),e)
                     ->
                     let lb =
                       let uu____72636 =
                         let uu____72637 = FStar_Syntax_Subst.compress t1  in
                         uu____72637.FStar_Syntax_Syntax.n  in
                       match uu____72636 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____72641) -> lb
                       | uu____72657 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____72667 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____72667
                         (fun def1  ->
                            ret
                              (let uu___1875_72673 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1875_72673.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1875_72673.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1875_72673.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1875_72673.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1875_72673.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1875_72673.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____72674 = fflb lb  in
                     bind uu____72674
                       (fun lb1  ->
                          let uu____72684 =
                            let uu____72689 =
                              let uu____72690 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____72690]  in
                            FStar_Syntax_Subst.open_term uu____72689 e  in
                          match uu____72684 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____72720 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____72720  in
                              let uu____72721 = ff1 e1  in
                              bind uu____72721
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____72768 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____72768
                         (fun def  ->
                            ret
                              (let uu___1893_72774 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1893_72774.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1893_72774.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1893_72774.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1893_72774.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1893_72774.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1893_72774.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____72775 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____72775 with
                      | (lbs1,e1) ->
                          let uu____72790 = mapM fflb lbs1  in
                          bind uu____72790
                            (fun lbs2  ->
                               let uu____72802 = ff e1  in
                               bind uu____72802
                                 (fun e2  ->
                                    let uu____72810 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____72810 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____72881 = ff t2  in
                     bind uu____72881
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____72912 = ff t2  in
                     bind uu____72912
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____72919 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___1917_72926 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___1917_72926.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___1917_72926.FStar_Syntax_Syntax.vars)
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
              let uu____72973 =
                FStar_TypeChecker_TcTerm.tc_term
                  (let uu___1930_72982 = env  in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___1930_72982.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___1930_72982.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___1930_72982.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___1930_72982.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_sig =
                       (uu___1930_72982.FStar_TypeChecker_Env.gamma_sig);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___1930_72982.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___1930_72982.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___1930_72982.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___1930_72982.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.attrtab =
                       (uu___1930_72982.FStar_TypeChecker_Env.attrtab);
                     FStar_TypeChecker_Env.is_pattern =
                       (uu___1930_72982.FStar_TypeChecker_Env.is_pattern);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___1930_72982.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___1930_72982.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___1930_72982.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___1930_72982.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___1930_72982.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___1930_72982.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___1930_72982.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___1930_72982.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___1930_72982.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax = true;
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___1930_72982.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.phase1 =
                       (uu___1930_72982.FStar_TypeChecker_Env.phase1);
                     FStar_TypeChecker_Env.failhard =
                       (uu___1930_72982.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___1930_72982.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.uvar_subtyping =
                       (uu___1930_72982.FStar_TypeChecker_Env.uvar_subtyping);
                     FStar_TypeChecker_Env.tc_term =
                       (uu___1930_72982.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.type_of =
                       (uu___1930_72982.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___1930_72982.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.check_type_of =
                       (uu___1930_72982.FStar_TypeChecker_Env.check_type_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___1930_72982.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (uu___1930_72982.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (uu___1930_72982.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.fv_delta_depths =
                       (uu___1930_72982.FStar_TypeChecker_Env.fv_delta_depths);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___1930_72982.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (uu___1930_72982.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.splice =
                       (uu___1930_72982.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.postprocess =
                       (uu___1930_72982.FStar_TypeChecker_Env.postprocess);
                     FStar_TypeChecker_Env.is_native_tactic =
                       (uu___1930_72982.FStar_TypeChecker_Env.is_native_tactic);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___1930_72982.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (uu___1930_72982.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (uu___1930_72982.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.nbe =
                       (uu___1930_72982.FStar_TypeChecker_Env.nbe)
                   }) t
                 in
              match uu____72973 with
              | (t1,lcomp,g) ->
                  let uu____72989 =
                    (let uu____72993 =
                       FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                     Prims.op_Negation uu____72993) ||
                      (let uu____72996 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____72996)
                     in
                  if uu____72989
                  then ret t1
                  else
                    (let rewrite_eq =
                       let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                       let uu____73007 = new_uvar "pointwise_rec" env typ  in
                       bind uu____73007
                         (fun uu____73024  ->
                            match uu____73024 with
                            | (ut,uvar_ut) ->
                                (log ps
                                   (fun uu____73037  ->
                                      let uu____73038 =
                                        FStar_Syntax_Print.term_to_string t1
                                         in
                                      let uu____73040 =
                                        FStar_Syntax_Print.term_to_string ut
                                         in
                                      FStar_Util.print2
                                        "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                        uu____73038 uu____73040);
                                 (let uu____73043 =
                                    let uu____73046 =
                                      let uu____73047 =
                                        FStar_TypeChecker_TcTerm.universe_of
                                          env typ
                                         in
                                      FStar_Syntax_Util.mk_eq2 uu____73047
                                        typ t1 ut
                                       in
                                    add_irrelevant_goal
                                      "pointwise_rec equation" env
                                      uu____73046 opts label1
                                     in
                                  bind uu____73043
                                    (fun uu____73051  ->
                                       let uu____73052 =
                                         bind tau
                                           (fun uu____73058  ->
                                              let ut1 =
                                                FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                  env ut
                                                 in
                                              log ps
                                                (fun uu____73064  ->
                                                   let uu____73065 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1
                                                      in
                                                   let uu____73067 =
                                                     FStar_Syntax_Print.term_to_string
                                                       ut1
                                                      in
                                                   FStar_Util.print2
                                                     "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                     uu____73065 uu____73067);
                                              ret ut1)
                                          in
                                       focus uu____73052))))
                        in
                     let uu____73070 = catch rewrite_eq  in
                     bind uu____73070
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
          let uu____73282 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____73282
            (fun t1  ->
               let uu____73290 =
                 f env
                   (let uu___2007_73298 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___2007_73298.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___2007_73298.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____73290
                 (fun uu____73314  ->
                    match uu____73314 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____73337 =
                               let uu____73338 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____73338.FStar_Syntax_Syntax.n  in
                             match uu____73337 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____73375 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____73375
                                   (fun uu____73397  ->
                                      match uu____73397 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____73413 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____73413
                                            (fun uu____73437  ->
                                               match uu____73437 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___1987_73467 =
                                                         t3  in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___1987_73467.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___1987_73467.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____73509 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____73509 with
                                  | (bs1,t') ->
                                      let uu____73524 =
                                        let uu____73531 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____73531 ctrl1 t'
                                         in
                                      bind uu____73524
                                        (fun uu____73546  ->
                                           match uu____73546 with
                                           | (t'',ctrl2) ->
                                               let uu____73561 =
                                                 let uu____73568 =
                                                   let uu___2000_73571 = t4
                                                      in
                                                   let uu____73574 =
                                                     let uu____73575 =
                                                       let uu____73594 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____73603 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____73594,
                                                         uu____73603, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____73575
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____73574;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___2000_73571.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___2000_73571.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____73568, ctrl2)  in
                                               ret uu____73561))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____73656 -> ret (t3, ctrl1))))

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
              let uu____73702 = ctrl_tac_fold f env ctrl t  in
              bind uu____73702
                (fun uu____73723  ->
                   match uu____73723 with
                   | (t1,ctrl1) ->
                       let uu____73738 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____73738
                         (fun uu____73762  ->
                            match uu____73762 with
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
                let uu____73853 =
                  let uu____73861 =
                    add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                      opts label1
                     in
                  bind uu____73861
                    (fun uu____73872  ->
                       let uu____73873 = ctrl t1  in
                       bind uu____73873
                         (fun res  ->
                            let uu____73899 = trivial ()  in
                            bind uu____73899 (fun uu____73908  -> ret res)))
                   in
                bind uu____73853
                  (fun uu____73926  ->
                     match uu____73926 with
                     | (should_rewrite,ctrl1) ->
                         if Prims.op_Negation should_rewrite
                         then ret (t1, ctrl1)
                         else
                           (let uu____73955 =
                              FStar_TypeChecker_TcTerm.tc_term
                                (let uu___2037_73964 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___2037_73964.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___2037_73964.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___2037_73964.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___2037_73964.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___2037_73964.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___2037_73964.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___2037_73964.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___2037_73964.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___2037_73964.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___2037_73964.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___2037_73964.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___2037_73964.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___2037_73964.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___2037_73964.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___2037_73964.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___2037_73964.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___2037_73964.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___2037_73964.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___2037_73964.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___2037_73964.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___2037_73964.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___2037_73964.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___2037_73964.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___2037_73964.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___2037_73964.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___2037_73964.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___2037_73964.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___2037_73964.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___2037_73964.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___2037_73964.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___2037_73964.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___2037_73964.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___2037_73964.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___2037_73964.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___2037_73964.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___2037_73964.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___2037_73964.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___2037_73964.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___2037_73964.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___2037_73964.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___2037_73964.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___2037_73964.FStar_TypeChecker_Env.nbe)
                                 }) t1
                               in
                            match uu____73955 with
                            | (t2,lcomp,g) ->
                                let uu____73975 =
                                  (let uu____73979 =
                                     FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                       lcomp
                                      in
                                   Prims.op_Negation uu____73979) ||
                                    (let uu____73982 =
                                       FStar_TypeChecker_Env.is_trivial g  in
                                     Prims.op_Negation uu____73982)
                                   in
                                if uu____73975
                                then ret (t2, globalStop)
                                else
                                  (let typ =
                                     lcomp.FStar_Syntax_Syntax.res_typ  in
                                   let uu____73998 =
                                     new_uvar "pointwise_rec" env typ  in
                                   bind uu____73998
                                     (fun uu____74019  ->
                                        match uu____74019 with
                                        | (ut,uvar_ut) ->
                                            (log ps
                                               (fun uu____74036  ->
                                                  let uu____74037 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t2
                                                     in
                                                  let uu____74039 =
                                                    FStar_Syntax_Print.term_to_string
                                                      ut
                                                     in
                                                  FStar_Util.print2
                                                    "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                    uu____74037 uu____74039);
                                             (let uu____74042 =
                                                let uu____74045 =
                                                  let uu____74046 =
                                                    FStar_TypeChecker_TcTerm.universe_of
                                                      env typ
                                                     in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____74046 typ t2 ut
                                                   in
                                                add_irrelevant_goal
                                                  "rewrite_rec equation" env
                                                  uu____74045 opts label1
                                                 in
                                              bind uu____74042
                                                (fun uu____74054  ->
                                                   let uu____74055 =
                                                     bind rewriter
                                                       (fun uu____74069  ->
                                                          let ut1 =
                                                            FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                              env ut
                                                             in
                                                          log ps
                                                            (fun uu____74075 
                                                               ->
                                                               let uu____74076
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   t2
                                                                  in
                                                               let uu____74078
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   ut1
                                                                  in
                                                               FStar_Util.print2
                                                                 "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                                 uu____74076
                                                                 uu____74078);
                                                          ret (ut1, ctrl1))
                                                      in
                                                   focus uu____74055)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term -> (Prims.bool * FStar_BigInt.t) tac) ->
    unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____74123 =
        bind get
          (fun ps  ->
             let uu____74133 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____74133 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____74171  ->
                       let uu____74172 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____74172);
                  bind dismiss_all
                    (fun uu____74177  ->
                       let uu____74178 =
                         let uu____74185 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____74185
                           keepGoing gt1
                          in
                       bind uu____74178
                         (fun uu____74195  ->
                            match uu____74195 with
                            | (gt',uu____74203) ->
                                (log ps
                                   (fun uu____74207  ->
                                      let uu____74208 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____74208);
                                 (let uu____74211 = push_goals gs  in
                                  bind uu____74211
                                    (fun uu____74216  ->
                                       let uu____74217 =
                                         let uu____74220 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____74220]  in
                                       add_goals uu____74217)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____74123
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____74245 =
        bind get
          (fun ps  ->
             let uu____74255 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____74255 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____74293  ->
                       let uu____74294 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____74294);
                  bind dismiss_all
                    (fun uu____74299  ->
                       let uu____74300 =
                         let uu____74303 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____74303 gt1
                          in
                       bind uu____74300
                         (fun gt'  ->
                            log ps
                              (fun uu____74311  ->
                                 let uu____74312 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____74312);
                            (let uu____74315 = push_goals gs  in
                             bind uu____74315
                               (fun uu____74320  ->
                                  let uu____74321 =
                                    let uu____74324 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____74324]  in
                                  add_goals uu____74321))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____74245
  
let (trefl : unit -> unit tac) =
  fun uu____74337  ->
    let uu____74340 =
      let uu____74343 = cur_goal ()  in
      bind uu____74343
        (fun g  ->
           let uu____74361 =
             let uu____74366 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____74366  in
           match uu____74361 with
           | FStar_Pervasives_Native.Some t ->
               let uu____74374 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____74374 with
                | (hd1,args) ->
                    let uu____74413 =
                      let uu____74426 =
                        let uu____74427 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____74427.FStar_Syntax_Syntax.n  in
                      (uu____74426, args)  in
                    (match uu____74413 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____74441::(l,uu____74443)::(r,uu____74445)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____74492 =
                           let uu____74496 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____74496 l r  in
                         bind uu____74492
                           (fun b  ->
                              if b
                              then solve' g FStar_Syntax_Util.exp_unit
                              else
                                (let l1 =
                                   let uu____74507 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____74507 l
                                    in
                                 let r1 =
                                   let uu____74509 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____74509 r
                                    in
                                 let uu____74510 =
                                   let uu____74514 =
                                     FStar_Tactics_Types.goal_env g  in
                                   do_unify uu____74514 l1 r1  in
                                 bind uu____74510
                                   (fun b1  ->
                                      if b1
                                      then
                                        solve' g FStar_Syntax_Util.exp_unit
                                      else
                                        (let uu____74524 =
                                           let uu____74526 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____74526 l1  in
                                         let uu____74527 =
                                           let uu____74529 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____74529 r1  in
                                         fail2
                                           "not a trivial equality ((%s) vs (%s))"
                                           uu____74524 uu____74527))))
                     | (hd2,uu____74532) ->
                         let uu____74549 =
                           let uu____74551 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____74551 t  in
                         fail1 "trefl: not an equality (%s)" uu____74549))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____74340
  
let (dup : unit -> unit tac) =
  fun uu____74568  ->
    let uu____74571 = cur_goal ()  in
    bind uu____74571
      (fun g  ->
         let uu____74577 =
           let uu____74584 = FStar_Tactics_Types.goal_env g  in
           let uu____74585 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____74584 uu____74585  in
         bind uu____74577
           (fun uu____74595  ->
              match uu____74595 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___2129_74605 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___2129_74605.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___2129_74605.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___2129_74605.FStar_Tactics_Types.is_guard);
                      FStar_Tactics_Types.label =
                        (uu___2129_74605.FStar_Tactics_Types.label)
                    }  in
                  bind __dismiss
                    (fun uu____74608  ->
                       let uu____74609 =
                         let uu____74612 = FStar_Tactics_Types.goal_env g  in
                         let uu____74613 =
                           let uu____74614 =
                             let uu____74615 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____74616 =
                               FStar_Tactics_Types.goal_type g  in
                             FStar_TypeChecker_TcTerm.universe_of uu____74615
                               uu____74616
                              in
                           let uu____74617 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____74618 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____74614 uu____74617 u
                             uu____74618
                            in
                         add_irrelevant_goal "dup equation" uu____74612
                           uu____74613 g.FStar_Tactics_Types.opts
                           g.FStar_Tactics_Types.label
                          in
                       bind uu____74609
                         (fun uu____74622  ->
                            let uu____74623 = add_goals [g']  in
                            bind uu____74623 (fun uu____74627  -> ret ())))))
  
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
              let uu____74753 = f x y  in
              if uu____74753 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____74776 -> (acc, l11, l21)  in
        let uu____74791 = aux [] l1 l2  in
        match uu____74791 with | (pr,t1,t2) -> ((FStar_List.rev pr), t1, t2)
  
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
      let uu____74897 = get_phi g1  in
      match uu____74897 with
      | FStar_Pervasives_Native.None  -> fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____74904 = get_phi g2  in
          (match uu____74904 with
           | FStar_Pervasives_Native.None  -> fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let uu____74917 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2)
                  in
               (match uu____74917 with
                | (gamma,r1,r2) ->
                    let t1 =
                      let uu____74948 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1)
                         in
                      close_forall_no_univs1 uu____74948 phi1  in
                    let t2 =
                      let uu____74958 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2)
                         in
                      close_forall_no_univs1 uu____74958 phi2  in
                    let uu____74967 =
                      set_solution g1 FStar_Syntax_Util.exp_unit  in
                    bind uu____74967
                      (fun uu____74972  ->
                         let uu____74973 =
                           set_solution g2 FStar_Syntax_Util.exp_unit  in
                         bind uu____74973
                           (fun uu____74980  ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2  in
                              let nenv =
                                let uu___2180_74985 =
                                  FStar_Tactics_Types.goal_env g1  in
                                let uu____74986 =
                                  FStar_Util.smap_create
                                    (Prims.parse_int "100")
                                   in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___2180_74985.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___2180_74985.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___2180_74985.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___2180_74985.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____74986;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___2180_74985.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___2180_74985.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___2180_74985.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___2180_74985.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___2180_74985.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___2180_74985.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___2180_74985.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___2180_74985.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___2180_74985.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___2180_74985.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___2180_74985.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___2180_74985.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___2180_74985.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___2180_74985.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___2180_74985.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___2180_74985.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___2180_74985.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___2180_74985.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___2180_74985.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___2180_74985.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___2180_74985.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___2180_74985.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___2180_74985.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___2180_74985.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___2180_74985.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___2180_74985.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___2180_74985.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___2180_74985.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___2180_74985.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___2180_74985.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___2180_74985.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___2180_74985.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___2180_74985.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___2180_74985.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___2180_74985.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___2180_74985.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___2180_74985.FStar_TypeChecker_Env.nbe)
                                }  in
                              let uu____74990 =
                                mk_irrelevant_goal "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                  g1.FStar_Tactics_Types.label
                                 in
                              bind uu____74990
                                (fun goal  ->
                                   mlog
                                     (fun uu____75000  ->
                                        let uu____75001 =
                                          goal_to_string_verbose g1  in
                                        let uu____75003 =
                                          goal_to_string_verbose g2  in
                                        let uu____75005 =
                                          goal_to_string_verbose goal  in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____75001 uu____75003 uu____75005)
                                     (fun uu____75009  -> ret goal))))))
  
let (join : unit -> unit tac) =
  fun uu____75017  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____75033 =
               set
                 (let uu___2195_75038 = ps  in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___2195_75038.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.main_goal =
                      (uu___2195_75038.FStar_Tactics_Types.main_goal);
                    FStar_Tactics_Types.all_implicits =
                      (uu___2195_75038.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___2195_75038.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___2195_75038.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___2195_75038.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___2195_75038.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___2195_75038.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___2195_75038.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___2195_75038.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___2195_75038.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___2195_75038.FStar_Tactics_Types.local_state)
                  })
                in
             bind uu____75033
               (fun uu____75041  ->
                  let uu____75042 = join_goals g1 g2  in
                  bind uu____75042 (fun g12  -> add_goals [g12]))
         | uu____75047 -> fail "join: less than 2 goals")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) tac)
  =
  fun t  ->
    let uu____75069 =
      let uu____75076 = cur_goal ()  in
      bind uu____75076
        (fun g  ->
           let uu____75086 =
             let uu____75095 = FStar_Tactics_Types.goal_env g  in
             __tc uu____75095 t  in
           bind uu____75086
             (fun uu____75123  ->
                match uu____75123 with
                | (t1,typ,guard) ->
                    let uu____75139 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____75139 with
                     | (hd1,args) ->
                         let uu____75188 =
                           let uu____75203 =
                             let uu____75204 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____75204.FStar_Syntax_Syntax.n  in
                           (uu____75203, args)  in
                         (match uu____75188 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____75225)::(q,uu____75227)::[]) when
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
                                let uu____75281 =
                                  let uu____75282 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____75282
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____75281
                                 in
                              let g2 =
                                let uu____75284 =
                                  let uu____75285 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____75285
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____75284
                                 in
                              bind __dismiss
                                (fun uu____75292  ->
                                   let uu____75293 = add_goals [g1; g2]  in
                                   bind uu____75293
                                     (fun uu____75302  ->
                                        let uu____75303 =
                                          let uu____75308 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____75309 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____75308, uu____75309)  in
                                        ret uu____75303))
                          | uu____75314 ->
                              let uu____75329 =
                                let uu____75331 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____75331 typ  in
                              fail1 "Not a disjunction: %s" uu____75329))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____75069
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____75366 =
      let uu____75369 = cur_goal ()  in
      bind uu____75369
        (fun g  ->
           FStar_Options.push ();
           (let uu____75382 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____75382);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___2232_75389 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___2232_75389.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___2232_75389.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___2232_75389.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___2232_75389.FStar_Tactics_Types.label)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____75366
  
let (top_env : unit -> env tac) =
  fun uu____75406  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____75421  ->
    let uu____75425 = cur_goal ()  in
    bind uu____75425
      (fun g  ->
         let uu____75432 =
           (FStar_Options.lax ()) ||
             (let uu____75435 = FStar_Tactics_Types.goal_env g  in
              uu____75435.FStar_TypeChecker_Env.lax)
            in
         ret uu____75432)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____75452 =
        mlog
          (fun uu____75457  ->
             let uu____75458 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____75458)
          (fun uu____75463  ->
             let uu____75464 = cur_goal ()  in
             bind uu____75464
               (fun goal  ->
                  let env =
                    let uu____75472 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____75472 ty  in
                  let uu____75473 = __tc_ghost env tm  in
                  bind uu____75473
                    (fun uu____75492  ->
                       match uu____75492 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____75506  ->
                                let uu____75507 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____75507)
                             (fun uu____75511  ->
                                mlog
                                  (fun uu____75514  ->
                                     let uu____75515 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____75515)
                                  (fun uu____75520  ->
                                     let uu____75521 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____75521
                                       (fun uu____75526  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____75452
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____75551 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____75557 =
              let uu____75564 =
                let uu____75565 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____75565
                 in
              new_uvar "uvar_env.2" env uu____75564  in
            bind uu____75557
              (fun uu____75582  ->
                 match uu____75582 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____75551
        (fun typ  ->
           let uu____75594 = new_uvar "uvar_env" env typ  in
           bind uu____75594
             (fun uu____75609  ->
                match uu____75609 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____75628 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____75647 -> g.FStar_Tactics_Types.opts
             | uu____75650 -> FStar_Options.peek ()  in
           let uu____75653 = FStar_Syntax_Util.head_and_args t  in
           match uu____75653 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____75673);
                FStar_Syntax_Syntax.pos = uu____75674;
                FStar_Syntax_Syntax.vars = uu____75675;_},uu____75676)
               ->
               let env1 =
                 let uu___2286_75718 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___2286_75718.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___2286_75718.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___2286_75718.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___2286_75718.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___2286_75718.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___2286_75718.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___2286_75718.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___2286_75718.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___2286_75718.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___2286_75718.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___2286_75718.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___2286_75718.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___2286_75718.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___2286_75718.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___2286_75718.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___2286_75718.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___2286_75718.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___2286_75718.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___2286_75718.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___2286_75718.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___2286_75718.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___2286_75718.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___2286_75718.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___2286_75718.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___2286_75718.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___2286_75718.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___2286_75718.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___2286_75718.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___2286_75718.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___2286_75718.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___2286_75718.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___2286_75718.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___2286_75718.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___2286_75718.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___2286_75718.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___2286_75718.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___2286_75718.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___2286_75718.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___2286_75718.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___2286_75718.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___2286_75718.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___2286_75718.FStar_TypeChecker_Env.nbe)
                 }  in
               let g =
                 FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false ""  in
               let uu____75722 =
                 let uu____75725 = bnorm_goal g  in [uu____75725]  in
               add_goals uu____75722
           | uu____75726 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____75628
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____75788 = if b then t2 else ret false  in
             bind uu____75788 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____75814 = trytac comp  in
      bind uu____75814
        (fun uu___613_75826  ->
           match uu___613_75826 with
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
        let uu____75868 =
          bind get
            (fun ps  ->
               let uu____75876 = __tc e t1  in
               bind uu____75876
                 (fun uu____75897  ->
                    match uu____75897 with
                    | (t11,ty1,g1) ->
                        let uu____75910 = __tc e t2  in
                        bind uu____75910
                          (fun uu____75931  ->
                             match uu____75931 with
                             | (t21,ty2,g2) ->
                                 let uu____75944 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____75944
                                   (fun uu____75951  ->
                                      let uu____75952 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____75952
                                        (fun uu____75960  ->
                                           let uu____75961 =
                                             do_unify e ty1 ty2  in
                                           let uu____75965 =
                                             do_unify e t11 t21  in
                                           tac_and uu____75961 uu____75965)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____75868
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____76013  ->
             let uu____76014 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____76014
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
        (fun uu____76048  ->
           let uu____76049 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____76049)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____76060 =
      mlog
        (fun uu____76065  ->
           let uu____76066 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____76066)
        (fun uu____76071  ->
           let uu____76072 = cur_goal ()  in
           bind uu____76072
             (fun g  ->
                let uu____76078 =
                  let uu____76087 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____76087 ty  in
                bind uu____76078
                  (fun uu____76099  ->
                     match uu____76099 with
                     | (ty1,uu____76109,guard) ->
                         let uu____76111 =
                           let uu____76114 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____76114 guard  in
                         bind uu____76111
                           (fun uu____76118  ->
                              let uu____76119 =
                                let uu____76123 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____76124 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____76123 uu____76124 ty1  in
                              bind uu____76119
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____76133 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____76133
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops]  in
                                      let ng =
                                        let uu____76140 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____76141 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____76140
                                          uu____76141
                                         in
                                      let nty =
                                        let uu____76143 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____76143 ty1  in
                                      let uu____76144 =
                                        let uu____76148 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____76148 ng nty  in
                                      bind uu____76144
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____76157 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____76157
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____76060
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) Prims.list tac)
  =
  fun s_tm  ->
    let uu____76231 =
      let uu____76240 = cur_goal ()  in
      bind uu____76240
        (fun g  ->
           let uu____76252 =
             let uu____76261 = FStar_Tactics_Types.goal_env g  in
             __tc uu____76261 s_tm  in
           bind uu____76252
             (fun uu____76279  ->
                match uu____76279 with
                | (s_tm1,s_ty,guard) ->
                    let uu____76297 =
                      let uu____76300 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____76300 guard  in
                    bind uu____76297
                      (fun uu____76313  ->
                         let uu____76314 =
                           FStar_Syntax_Util.head_and_args' s_ty  in
                         match uu____76314 with
                         | (h,args) ->
                             let uu____76359 =
                               let uu____76366 =
                                 let uu____76367 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____76367.FStar_Syntax_Syntax.n  in
                               match uu____76366 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____76382;
                                      FStar_Syntax_Syntax.vars = uu____76383;_},us)
                                   -> ret (fv, us)
                               | uu____76393 -> fail "type is not an fv"  in
                             bind uu____76359
                               (fun uu____76414  ->
                                  match uu____76414 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____76430 =
                                        let uu____76433 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____76433 t_lid
                                         in
                                      (match uu____76430 with
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
                                                  (fun uu____76484  ->
                                                     let uu____76485 =
                                                       FStar_Syntax_Subst.open_term
                                                         t_ps t_ty
                                                        in
                                                     match uu____76485 with
                                                     | (t_ps1,t_ty1) ->
                                                         let uu____76500 =
                                                           mapM
                                                             (fun c_lid  ->
                                                                let uu____76528
                                                                  =
                                                                  let uu____76531
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                  FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____76531
                                                                    c_lid
                                                                   in
                                                                match uu____76528
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
                                                                    uu____76605
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
                                                                    let uu____76610
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____76610
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____76633
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____76633
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____76676
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs
                                                                     in
                                                                    (match uu____76676
                                                                    with
                                                                    | 
                                                                    (d_ps,bs1)
                                                                    ->
                                                                    let uu____76749
                                                                    =
                                                                    let uu____76751
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp  in
                                                                    Prims.op_Negation
                                                                    uu____76751
                                                                     in
                                                                    failwhen
                                                                    uu____76749
                                                                    "not total?"
                                                                    (fun
                                                                    uu____76770
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
                                                                    uu___614_76787
                                                                    =
                                                                    match uu___614_76787
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____76791)
                                                                    -> true
                                                                    | 
                                                                    uu____76794
                                                                    -> false
                                                                     in
                                                                    let uu____76798
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____76798
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
                                                                    uu____76932
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
                                                                    uu____76994
                                                                     ->
                                                                    match uu____76994
                                                                    with
                                                                    | 
                                                                    ((bv,uu____77014),
                                                                    (t,uu____77016))
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
                                                                    uu____77086
                                                                     ->
                                                                    match uu____77086
                                                                    with
                                                                    | 
                                                                    ((bv,uu____77113),
                                                                    (t,uu____77115))
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
                                                                    uu____77174
                                                                     ->
                                                                    match uu____77174
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
                                                                    let uu____77229
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___2450_77246
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___2450_77246.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___2450_77246.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___2450_77246.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___2450_77246.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___2450_77246.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___2450_77246.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___2450_77246.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___2450_77246.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___2450_77246.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___2450_77246.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___2450_77246.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___2450_77246.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___2450_77246.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___2450_77246.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___2450_77246.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___2450_77246.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___2450_77246.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___2450_77246.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___2450_77246.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___2450_77246.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___2450_77246.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___2450_77246.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___2450_77246.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___2450_77246.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___2450_77246.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___2450_77246.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___2450_77246.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___2450_77246.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___2450_77246.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___2450_77246.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___2450_77246.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___2450_77246.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___2450_77246.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___2450_77246.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___2450_77246.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___2450_77246.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___2450_77246.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___2450_77246.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___2450_77246.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___2450_77246.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___2450_77246.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___2450_77246.FStar_TypeChecker_Env.nbe)
                                                                    }) s_ty
                                                                    pat  in
                                                                    match uu____77229
                                                                    with
                                                                    | 
                                                                    (uu____77260,uu____77261,uu____77262,pat_t,uu____77264,_guard_pat)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____77271
                                                                    =
                                                                    let uu____77272
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____77272
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____77271
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____77277
                                                                    =
                                                                    let uu____77286
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____77286]
                                                                     in
                                                                    let uu____77305
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____77277
                                                                    uu____77305
                                                                     in
                                                                    let nty =
                                                                    let uu____77311
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____77311
                                                                     in
                                                                    let uu____77314
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____77314
                                                                    (fun
                                                                    uu____77344
                                                                     ->
                                                                    match uu____77344
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
                                                                    let uu____77371
                                                                    =
                                                                    let uu____77382
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____77382]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____77371
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____77418
                                                                    =
                                                                    let uu____77429
                                                                    =
                                                                    let uu____77434
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2)  in
                                                                    (fv1,
                                                                    uu____77434)
                                                                     in
                                                                    (g', br,
                                                                    uu____77429)
                                                                     in
                                                                    ret
                                                                    uu____77418))))))
                                                                    | 
                                                                    uu____77455
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                             c_lids
                                                            in
                                                         bind uu____76500
                                                           (fun goal_brs  ->
                                                              let uu____77505
                                                                =
                                                                FStar_List.unzip3
                                                                  goal_brs
                                                                 in
                                                              match uu____77505
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
                                                                  let uu____77578
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                  bind
                                                                    uu____77578
                                                                    (
                                                                    fun
                                                                    uu____77589
                                                                     ->
                                                                    let uu____77590
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____77590
                                                                    (fun
                                                                    uu____77600
                                                                     ->
                                                                    ret infos))))
                                            | uu____77607 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____76231
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____77656::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____77686 = init xs  in x :: uu____77686
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____77699 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      let t3 = FStar_Syntax_Util.unlazy_emb t2  in
      match t3.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____77708) -> inspect t4
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____77774 = last args  in
          (match uu____77774 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____77804 =
                 let uu____77805 =
                   let uu____77810 =
                     let uu____77811 =
                       let uu____77816 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____77816  in
                     uu____77811 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____77810, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____77805  in
               FStar_All.pipe_left ret uu____77804)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____77827,uu____77828) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
          let uu____77881 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____77881 with
           | (bs1,t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____77923 =
                      let uu____77924 =
                        let uu____77929 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____77929)  in
                      FStar_Reflection_Data.Tv_Abs uu____77924  in
                    FStar_All.pipe_left ret uu____77923))
      | FStar_Syntax_Syntax.Tm_type uu____77932 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____77957 ->
          let uu____77972 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____77972 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____78003 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____78003 with
           | (b',t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____78056 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____78069 =
            let uu____78070 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____78070  in
          FStar_All.pipe_left ret uu____78069
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____78091 =
            let uu____78092 =
              let uu____78097 =
                let uu____78098 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____78098  in
              (uu____78097, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____78092  in
          FStar_All.pipe_left ret uu____78091
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____78138 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____78143 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____78143 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____78196 ->
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
             | FStar_Util.Inr uu____78238 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____78242 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____78242 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____78262 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____78268 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____78323 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____78323
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____78344 =
                  let uu____78351 =
                    FStar_List.map
                      (fun uu____78364  ->
                         match uu____78364 with
                         | (p1,uu____78373) -> inspect_pat p1) ps
                     in
                  (fv, uu____78351)  in
                FStar_Reflection_Data.Pat_Cons uu____78344
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
              (fun uu___615_78469  ->
                 match uu___615_78469 with
                 | (pat,uu____78491,t5) ->
                     let uu____78509 = inspect_pat pat  in (uu____78509, t5))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____78518 ->
          ((let uu____78520 =
              let uu____78526 =
                let uu____78528 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____78530 = FStar_Syntax_Print.term_to_string t3  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____78528 uu____78530
                 in
              (FStar_Errors.Warning_CantInspect, uu____78526)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____78520);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____77699
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____78548 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____78548
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____78552 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____78552
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____78556 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____78556
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____78563 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____78563
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____78588 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____78588
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____78605 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____78605
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____78624 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____78624
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____78628 =
          let uu____78629 =
            let uu____78636 =
              let uu____78637 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____78637  in
            FStar_Syntax_Syntax.mk uu____78636  in
          uu____78629 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____78628
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____78642 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____78642
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____78653 =
          let uu____78654 =
            let uu____78661 =
              let uu____78662 =
                let uu____78676 =
                  let uu____78679 =
                    let uu____78680 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____78680]  in
                  FStar_Syntax_Subst.close uu____78679 t2  in
                ((false, [lb]), uu____78676)  in
              FStar_Syntax_Syntax.Tm_let uu____78662  in
            FStar_Syntax_Syntax.mk uu____78661  in
          uu____78654 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____78653
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____78722 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____78722 with
         | (lbs,body) ->
             let uu____78737 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____78737)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____78774 =
                let uu____78775 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____78775  in
              FStar_All.pipe_left wrap uu____78774
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____78782 =
                let uu____78783 =
                  let uu____78797 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____78815 = pack_pat p1  in
                         (uu____78815, false)) ps
                     in
                  (fv, uu____78797)  in
                FStar_Syntax_Syntax.Pat_cons uu____78783  in
              FStar_All.pipe_left wrap uu____78782
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
            (fun uu___616_78864  ->
               match uu___616_78864 with
               | (pat,t1) ->
                   let uu____78881 = pack_pat pat  in
                   (uu____78881, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____78929 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____78929
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____78957 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____78957
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____79003 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____79003
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____79042 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____79042
  
let (lget :
  FStar_Reflection_Data.typ -> Prims.string -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun k  ->
      let uu____79062 =
        bind get
          (fun ps  ->
             let uu____79068 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____79068 with
             | FStar_Pervasives_Native.None  -> fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
      FStar_All.pipe_left (wrap_err "lget") uu____79062
  
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit tac)
  =
  fun _ty  ->
    fun k  ->
      fun t  ->
        let uu____79102 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___2748_79109 = ps  in
                 let uu____79110 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t
                    in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___2748_79109.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___2748_79109.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___2748_79109.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___2748_79109.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___2748_79109.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___2748_79109.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___2748_79109.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___2748_79109.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___2748_79109.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___2748_79109.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___2748_79109.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___2748_79109.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____79110
                 }  in
               set ps1)
           in
        FStar_All.pipe_left (wrap_err "lset") uu____79102
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal * FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun typ  ->
      let uu____79137 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____79137 with
      | (u,ctx_uvars,g_u) ->
          let uu____79170 = FStar_List.hd ctx_uvars  in
          (match uu____79170 with
           | (ctx_uvar,uu____79184) ->
               let g =
                 let uu____79186 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____79186 false
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
        let uu____79209 = goal_of_goal_ty env typ  in
        match uu____79209 with
        | (g,g_u) ->
            let ps =
              let uu____79221 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "TacVerbose")
                 in
              let uu____79224 = FStar_Util.psmap_empty ()  in
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
                FStar_Tactics_Types.tac_verb_dbg = uu____79221;
                FStar_Tactics_Types.local_state = uu____79224
              }  in
            let uu____79234 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____79234)
  