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
    let uu____63874 =
      let uu____63875 = FStar_Tactics_Types.goal_env g  in
      let uu____63876 = FStar_Tactics_Types.goal_type g  in
      bnorm uu____63875 uu____63876  in
    FStar_Tactics_Types.goal_with_type g uu____63874
  
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
      let uu____63990 = FStar_Options.tactics_failhard ()  in
      if uu____63990
      then run t p
      else
        (try (fun uu___640_64000  -> match () with | () -> run t p) ()
         with
         | FStar_Errors.Err (uu____64009,msg) ->
             FStar_Tactics_Result.Failed
               ((FStar_Tactics_Types.TacticFailure msg), p)
         | FStar_Errors.Error (uu____64013,msg,uu____64015) ->
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
           let uu____64095 = run t1 p  in
           match uu____64095 with
           | FStar_Tactics_Result.Success (a,q) ->
               let uu____64102 = t2 a  in run uu____64102 q
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
    let uu____64125 =
      FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head  in
    match uu____64125 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (check_goal_solved :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun goal  -> get_uvar_solved goal.FStar_Tactics_Types.goal_ctx_uvar 
let (goal_to_string_verbose : FStar_Tactics_Types.goal -> Prims.string) =
  fun g  ->
    let uu____64147 =
      FStar_Syntax_Print.ctx_uvar_to_string
        g.FStar_Tactics_Types.goal_ctx_uvar
       in
    let uu____64149 =
      let uu____64151 = check_goal_solved g  in
      match uu____64151 with
      | FStar_Pervasives_Native.None  -> ""
      | FStar_Pervasives_Native.Some t ->
          let uu____64157 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "\tGOAL ALREADY SOLVED!: %s" uu____64157
       in
    FStar_Util.format2 "%s%s\n" uu____64147 uu____64149
  
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
            let uu____64204 = FStar_Options.print_implicits ()  in
            if uu____64204
            then
              let uu____64208 = FStar_Tactics_Types.goal_env g  in
              let uu____64209 = FStar_Tactics_Types.goal_witness g  in
              tts uu____64208 uu____64209
            else
              (let uu____64212 =
                 get_uvar_solved g.FStar_Tactics_Types.goal_ctx_uvar  in
               match uu____64212 with
               | FStar_Pervasives_Native.None  -> "_"
               | FStar_Pervasives_Native.Some t ->
                   let uu____64218 = FStar_Tactics_Types.goal_env g  in
                   let uu____64219 = FStar_Tactics_Types.goal_witness g  in
                   tts uu____64218 uu____64219)
             in
          let num =
            match maybe_num with
            | FStar_Pervasives_Native.None  -> ""
            | FStar_Pervasives_Native.Some (i,n1) ->
                let uu____64242 = FStar_Util.string_of_int i  in
                let uu____64244 = FStar_Util.string_of_int n1  in
                FStar_Util.format2 " %s/%s" uu____64242 uu____64244
             in
          let maybe_label =
            match g.FStar_Tactics_Types.label with
            | "" -> ""
            | l -> Prims.op_Hat " (" (Prims.op_Hat l ")")  in
          let actual_goal =
            if ps.FStar_Tactics_Types.tac_verb_dbg
            then goal_to_string_verbose g
            else
              (let uu____64262 =
                 FStar_Syntax_Print.binders_to_string ", "
                   (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
                  in
               let uu____64265 =
                 let uu____64267 = FStar_Tactics_Types.goal_env g  in
                 tts uu____64267
                   (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                  in
               FStar_Util.format3 "%s |- %s : %s\n" uu____64262 w uu____64265)
             in
          FStar_Util.format4 "%s%s%s:\n%s\n" kind num maybe_label actual_goal
  
let (tacprint : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      let uu____64294 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____64294
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____64319 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____64319
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____64351 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____64351
  
let (comp_to_typ : FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____64361) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____64371) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (get_phi :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun g  ->
    let uu____64391 =
      let uu____64392 = FStar_Tactics_Types.goal_env g  in
      let uu____64393 = FStar_Tactics_Types.goal_type g  in
      FStar_TypeChecker_Normalize.unfold_whnf uu____64392 uu____64393  in
    FStar_Syntax_Util.un_squash uu____64391
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  -> let uu____64402 = get_phi g  in FStar_Option.isSome uu____64402 
let (print : Prims.string -> unit tac) = fun msg  -> tacprint msg; ret () 
let (debugging : unit -> Prims.bool tac) =
  fun uu____64426  ->
    bind get
      (fun ps  ->
         let uu____64434 =
           FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
             (FStar_Options.Other "Tac")
            in
         ret uu____64434)
  
let (ps_to_string :
  (Prims.string * FStar_Tactics_Types.proofstate) -> Prims.string) =
  fun uu____64449  ->
    match uu____64449 with
    | (msg,ps) ->
        let p_imp imp =
          FStar_Syntax_Print.uvar_to_string
            (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
           in
        let n_active = FStar_List.length ps.FStar_Tactics_Types.goals  in
        let n_smt = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
        let n1 = n_active + n_smt  in
        let uu____64471 =
          let uu____64475 =
            let uu____64479 =
              let uu____64481 =
                FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
              FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____64481
                msg
               in
            let uu____64484 =
              let uu____64488 =
                if
                  ps.FStar_Tactics_Types.entry_range <>
                    FStar_Range.dummyRange
                then
                  let uu____64492 =
                    FStar_Range.string_of_def_range
                      ps.FStar_Tactics_Types.entry_range
                     in
                  FStar_Util.format1 "Location: %s\n" uu____64492
                else ""  in
              let uu____64498 =
                let uu____64502 =
                  let uu____64504 =
                    FStar_TypeChecker_Env.debug
                      ps.FStar_Tactics_Types.main_context
                      (FStar_Options.Other "Imp")
                     in
                  if uu____64504
                  then
                    let uu____64509 =
                      FStar_Common.string_of_list p_imp
                        ps.FStar_Tactics_Types.all_implicits
                       in
                    FStar_Util.format1 "Imps: %s\n" uu____64509
                  else ""  in
                [uu____64502]  in
              uu____64488 :: uu____64498  in
            uu____64479 :: uu____64484  in
          let uu____64519 =
            let uu____64523 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "Goal"
                       (FStar_Pervasives_Native.Some
                          (((Prims.parse_int "1") + i), n1)) ps g)
                ps.FStar_Tactics_Types.goals
               in
            let uu____64543 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "SMT Goal"
                       (FStar_Pervasives_Native.Some
                          ((((Prims.parse_int "1") + n_active) + i), n1)) ps
                       g) ps.FStar_Tactics_Types.smt_goals
               in
            FStar_List.append uu____64523 uu____64543  in
          FStar_List.append uu____64475 uu____64519  in
        FStar_String.concat "" uu____64471
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      let uu____64573 =
        let uu____64574 = FStar_Tactics_Types.goal_env g  in
        FStar_TypeChecker_Env.all_binders uu____64574  in
      let uu____64575 =
        let uu____64580 =
          let uu____64581 = FStar_Tactics_Types.goal_env g  in
          FStar_TypeChecker_Env.dsenv uu____64581  in
        FStar_Syntax_Print.binders_to_json uu____64580  in
      FStar_All.pipe_right uu____64573 uu____64575  in
    let uu____64582 =
      let uu____64590 =
        let uu____64598 =
          let uu____64604 =
            let uu____64605 =
              let uu____64613 =
                let uu____64619 =
                  let uu____64620 =
                    let uu____64622 = FStar_Tactics_Types.goal_env g  in
                    let uu____64623 = FStar_Tactics_Types.goal_witness g  in
                    tts uu____64622 uu____64623  in
                  FStar_Util.JsonStr uu____64620  in
                ("witness", uu____64619)  in
              let uu____64626 =
                let uu____64634 =
                  let uu____64640 =
                    let uu____64641 =
                      let uu____64643 = FStar_Tactics_Types.goal_env g  in
                      let uu____64644 = FStar_Tactics_Types.goal_type g  in
                      tts uu____64643 uu____64644  in
                    FStar_Util.JsonStr uu____64641  in
                  ("type", uu____64640)  in
                [uu____64634;
                ("label", (FStar_Util.JsonStr (g.FStar_Tactics_Types.label)))]
                 in
              uu____64613 :: uu____64626  in
            FStar_Util.JsonAssoc uu____64605  in
          ("goal", uu____64604)  in
        [uu____64598]  in
      ("hyps", g_binders) :: uu____64590  in
    FStar_Util.JsonAssoc uu____64582
  
let (ps_to_json :
  (Prims.string * FStar_Tactics_Types.proofstate) -> FStar_Util.json) =
  fun uu____64698  ->
    match uu____64698 with
    | (msg,ps) ->
        let uu____64708 =
          let uu____64716 =
            let uu____64724 =
              let uu____64732 =
                let uu____64740 =
                  let uu____64746 =
                    let uu____64747 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____64747  in
                  ("goals", uu____64746)  in
                let uu____64752 =
                  let uu____64760 =
                    let uu____64766 =
                      let uu____64767 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____64767  in
                    ("smt-goals", uu____64766)  in
                  [uu____64760]  in
                uu____64740 :: uu____64752  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____64732
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____64724  in
          let uu____64801 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____64817 =
                let uu____64823 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____64823)  in
              [uu____64817]
            else []  in
          FStar_List.append uu____64716 uu____64801  in
        FStar_Util.JsonAssoc uu____64708
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____64863  ->
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
         (let uu____64894 = FStar_Tactics_Types.subst_proof_state subst1 ps
             in
          dump_proofstate uu____64894 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let traise : 'a . Prims.exn -> 'a tac =
  fun e  -> mk_tac (fun ps  -> FStar_Tactics_Result.Failed (e, ps)) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____64967 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____64967
          then dump_proofstate ps (Prims.op_Hat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed
           ((FStar_Tactics_Types.TacticFailure msg), ps))
  
let fail1 : 'Auu____64981 . Prims.string -> Prims.string -> 'Auu____64981 tac
  =
  fun msg  ->
    fun x  -> let uu____64998 = FStar_Util.format1 msg x  in fail uu____64998
  
let fail2 :
  'Auu____65009 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____65009 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        let uu____65033 = FStar_Util.format2 msg x y  in fail uu____65033
  
let fail3 :
  'Auu____65046 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____65046 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____65077 = FStar_Util.format3 msg x y z  in fail uu____65077
  
let fail4 :
  'Auu____65092 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____65092 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____65130 = FStar_Util.format4 msg x y z w  in
            fail uu____65130
  
let catch : 'a . 'a tac -> (Prims.exn,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____65165 = run t ps  in
         match uu____65165 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___802_65189 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___802_65189.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___802_65189.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___802_65189.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___802_65189.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___802_65189.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___802_65189.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___802_65189.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___802_65189.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___802_65189.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___802_65189.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___802_65189.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (uu___802_65189.FStar_Tactics_Types.local_state)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let recover : 'a . 'a tac -> (Prims.exn,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let uu____65228 = run t ps  in
         match uu____65228 with
         | FStar_Tactics_Result.Success (a,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inr a), q)
         | FStar_Tactics_Result.Failed (m,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inl m), q))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____65276 = catch t  in
    bind uu____65276
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____65303 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try
           (fun uu___828_65335  ->
              match () with
              | () -> let uu____65340 = trytac t  in run uu____65340 ps) ()
         with
         | FStar_Errors.Err (uu____65356,msg) ->
             (log ps
                (fun uu____65362  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____65368,msg,uu____65370) ->
             (log ps
                (fun uu____65375  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____65412 = run t ps  in
           match uu____65412 with
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
  fun p  -> mk_tac (fun uu____65436  -> FStar_Tactics_Result.Success ((), p)) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___863_65451 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___863_65451.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___863_65451.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___863_65451.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___863_65451.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___863_65451.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___863_65451.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___863_65451.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___863_65451.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___863_65451.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___863_65451.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___863_65451.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___863_65451.FStar_Tactics_Types.local_state)
            }))
  
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____65475 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____65475
         then
           let uu____65479 = FStar_Syntax_Print.term_to_string t1  in
           let uu____65481 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____65479
             uu____65481
         else ());
        (try
           (fun uu___871_65492  ->
              match () with
              | () ->
                  let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
                  ((let uu____65500 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____65500
                    then
                      let uu____65504 =
                        FStar_Common.string_of_option
                          (FStar_TypeChecker_Rel.guard_to_string env) res
                         in
                      let uu____65506 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____65508 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.print3
                        "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____65504
                        uu____65506 uu____65508
                    else ());
                   (match res with
                    | FStar_Pervasives_Native.None  -> ret false
                    | FStar_Pervasives_Native.Some g ->
                        let uu____65519 =
                          add_implicits g.FStar_TypeChecker_Env.implicits  in
                        bind uu____65519 (fun uu____65524  -> ret true)))) ()
         with
         | FStar_Errors.Err (uu____65534,msg) ->
             mlog
               (fun uu____65540  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____65543  -> ret false)
         | FStar_Errors.Error (uu____65546,msg,r) ->
             mlog
               (fun uu____65554  ->
                  let uu____65555 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____65555) (fun uu____65559  -> ret false))
  
let (compress_implicits : unit tac) =
  bind get
    (fun ps  ->
       let imps = ps.FStar_Tactics_Types.all_implicits  in
       let g =
         let uu___897_65573 = FStar_TypeChecker_Env.trivial_guard  in
         {
           FStar_TypeChecker_Env.guard_f =
             (uu___897_65573.FStar_TypeChecker_Env.guard_f);
           FStar_TypeChecker_Env.deferred =
             (uu___897_65573.FStar_TypeChecker_Env.deferred);
           FStar_TypeChecker_Env.univ_ineqs =
             (uu___897_65573.FStar_TypeChecker_Env.univ_ineqs);
           FStar_TypeChecker_Env.implicits = imps
         }  in
       let g1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g
          in
       let ps' =
         let uu___901_65576 = ps  in
         {
           FStar_Tactics_Types.main_context =
             (uu___901_65576.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___901_65576.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (g1.FStar_TypeChecker_Env.implicits);
           FStar_Tactics_Types.goals =
             (uu___901_65576.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___901_65576.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___901_65576.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___901_65576.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___901_65576.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___901_65576.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___901_65576.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___901_65576.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___901_65576.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___901_65576.FStar_Tactics_Types.local_state)
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
          (fun uu____65603  ->
             (let uu____65605 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____65605
              then
                (FStar_Options.push ();
                 (let uu____65610 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____65614 = __do_unify env t1 t2  in
              bind uu____65614
                (fun r  ->
                   (let uu____65625 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____65625 then FStar_Options.pop () else ());
                   ret r)))
  
let (remove_solved_goals : unit tac) =
  bind get
    (fun ps  ->
       let ps' =
         let uu___916_65639 = ps  in
         let uu____65640 =
           FStar_List.filter
             (fun g  ->
                let uu____65646 = check_goal_solved g  in
                FStar_Option.isNone uu____65646) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___916_65639.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___916_65639.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___916_65639.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____65640;
           FStar_Tactics_Types.smt_goals =
             (uu___916_65639.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___916_65639.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___916_65639.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___916_65639.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___916_65639.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___916_65639.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___916_65639.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___916_65639.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___916_65639.FStar_Tactics_Types.local_state)
         }  in
       set ps')
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____65664 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____65664 with
      | FStar_Pervasives_Native.Some uu____65669 ->
          let uu____65670 =
            let uu____65672 = goal_to_string_verbose goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____65672  in
          fail uu____65670
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____65693 = FStar_Tactics_Types.goal_env goal  in
      let uu____65694 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____65693 solution uu____65694
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____65701 =
         let uu___929_65702 = p  in
         let uu____65703 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___929_65702.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___929_65702.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___929_65702.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____65703;
           FStar_Tactics_Types.smt_goals =
             (uu___929_65702.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___929_65702.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___929_65702.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___929_65702.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___929_65702.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___929_65702.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___929_65702.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___929_65702.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___929_65702.FStar_Tactics_Types.local_state)
         }  in
       set uu____65701)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      mlog
        (fun uu____65725  ->
           let uu____65726 =
             let uu____65728 = FStar_Tactics_Types.goal_witness goal  in
             FStar_Syntax_Print.term_to_string uu____65728  in
           let uu____65729 = FStar_Syntax_Print.term_to_string solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____65726 uu____65729)
        (fun uu____65734  ->
           let uu____65735 = trysolve goal solution  in
           bind uu____65735
             (fun b  ->
                if b
                then bind __dismiss (fun uu____65747  -> remove_solved_goals)
                else
                  (let uu____65750 =
                     let uu____65752 =
                       let uu____65754 = FStar_Tactics_Types.goal_env goal
                          in
                       tts uu____65754 solution  in
                     let uu____65755 =
                       let uu____65757 = FStar_Tactics_Types.goal_env goal
                          in
                       let uu____65758 =
                         FStar_Tactics_Types.goal_witness goal  in
                       tts uu____65757 uu____65758  in
                     let uu____65759 =
                       let uu____65761 = FStar_Tactics_Types.goal_env goal
                          in
                       let uu____65762 = FStar_Tactics_Types.goal_type goal
                          in
                       tts uu____65761 uu____65762  in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____65752 uu____65755 uu____65759
                      in
                   fail uu____65750)))
  
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____65779 = set_solution goal solution  in
      bind uu____65779
        (fun uu____65783  ->
           bind __dismiss (fun uu____65785  -> remove_solved_goals))
  
let (set_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___945_65804 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___945_65804.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___945_65804.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___945_65804.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals = gs;
              FStar_Tactics_Types.smt_goals =
                (uu___945_65804.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___945_65804.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___945_65804.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___945_65804.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___945_65804.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___945_65804.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___945_65804.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___945_65804.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___945_65804.FStar_Tactics_Types.local_state)
            }))
  
let (set_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___949_65823 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___949_65823.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___949_65823.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___949_65823.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___949_65823.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals = gs;
              FStar_Tactics_Types.depth =
                (uu___949_65823.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___949_65823.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___949_65823.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___949_65823.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___949_65823.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___949_65823.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___949_65823.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___949_65823.FStar_Tactics_Types.local_state)
            }))
  
let (dismiss_all : unit tac) = set_goals [] 
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____65839 = FStar_Options.defensive ()  in
    if uu____65839
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____65849 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____65849)
         in
      let b2 =
        b1 &&
          (let uu____65853 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____65853)
         in
      let rec aux b3 e =
        let uu____65868 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____65868 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____65888 =
        (let uu____65892 = aux b2 env  in Prims.op_Negation uu____65892) &&
          (let uu____65895 = FStar_ST.op_Bang nwarn  in
           uu____65895 < (Prims.parse_int "5"))
         in
      (if uu____65888
       then
         ((let uu____65921 =
             let uu____65922 = FStar_Tactics_Types.goal_type g  in
             uu____65922.FStar_Syntax_Syntax.pos  in
           let uu____65925 =
             let uu____65931 =
               let uu____65933 = goal_to_string_verbose g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____65933
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____65931)  in
           FStar_Errors.log_issue uu____65921 uu____65925);
          (let uu____65937 =
             let uu____65939 = FStar_ST.op_Bang nwarn  in
             uu____65939 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____65937))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___971_66008 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___971_66008.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___971_66008.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___971_66008.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___971_66008.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___971_66008.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___971_66008.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___971_66008.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___971_66008.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___971_66008.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___971_66008.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___971_66008.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___971_66008.FStar_Tactics_Types.local_state)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___976_66029 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___976_66029.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___976_66029.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___976_66029.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___976_66029.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___976_66029.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___976_66029.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___976_66029.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___976_66029.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___976_66029.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___976_66029.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___976_66029.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___976_66029.FStar_Tactics_Types.local_state)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___981_66050 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___981_66050.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___981_66050.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___981_66050.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___981_66050.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___981_66050.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___981_66050.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___981_66050.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___981_66050.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___981_66050.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___981_66050.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___981_66050.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___981_66050.FStar_Tactics_Types.local_state)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___986_66071 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___986_66071.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___986_66071.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___986_66071.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___986_66071.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___986_66071.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___986_66071.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___986_66071.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___986_66071.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___986_66071.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___986_66071.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___986_66071.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___986_66071.FStar_Tactics_Types.local_state)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____66083  -> add_goals [g]) 
let (new_uvar :
  Prims.string ->
    env ->
      FStar_Reflection_Data.typ ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar) tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____66114 =
          FStar_TypeChecker_Env.new_implicit_var_aux reason
            typ.FStar_Syntax_Syntax.pos env typ
            FStar_Syntax_Syntax.Allow_untyped FStar_Pervasives_Native.None
           in
        match uu____66114 with
        | (u,ctx_uvar,g_u) ->
            let uu____66152 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____66152
              (fun uu____66161  ->
                 let uu____66162 =
                   let uu____66167 =
                     let uu____66168 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____66168  in
                   (u, uu____66167)  in
                 ret uu____66162)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____66189 = FStar_Syntax_Util.un_squash t1  in
    match uu____66189 with
    | FStar_Pervasives_Native.Some t' ->
        let t'1 = FStar_Syntax_Util.unascribe t'  in
        let uu____66201 =
          let uu____66202 = FStar_Syntax_Subst.compress t'1  in
          uu____66202.FStar_Syntax_Syntax.n  in
        (match uu____66201 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____66207 -> false)
    | uu____66209 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____66222 = FStar_Syntax_Util.un_squash t  in
    match uu____66222 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____66233 =
          let uu____66234 = FStar_Syntax_Subst.compress t'  in
          uu____66234.FStar_Syntax_Syntax.n  in
        (match uu____66233 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____66239 -> false)
    | uu____66241 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____66254  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____66266 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____66266 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____66273 = goal_to_string_verbose hd1  in
                    let uu____66275 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____66273 uu____66275);
                   ret hd1)))
  
let (tadmit_t : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____66288 =
      bind get
        (fun ps  ->
           let uu____66294 = cur_goal ()  in
           bind uu____66294
             (fun g  ->
                (let uu____66301 =
                   let uu____66302 = FStar_Tactics_Types.goal_type g  in
                   uu____66302.FStar_Syntax_Syntax.pos  in
                 let uu____66305 =
                   let uu____66311 =
                     let uu____66313 =
                       goal_to_string "" FStar_Pervasives_Native.None ps g
                        in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____66313
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____66311)  in
                 FStar_Errors.log_issue uu____66301 uu____66305);
                solve' g t))
       in
    FStar_All.pipe_left (wrap_err "tadmit_t") uu____66288
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____66336  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___1031_66347 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___1031_66347.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___1031_66347.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___1031_66347.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___1031_66347.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___1031_66347.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___1031_66347.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___1031_66347.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___1031_66347.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___1031_66347.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___1031_66347.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___1031_66347.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (uu___1031_66347.FStar_Tactics_Types.local_state)
           }  in
         let uu____66349 = set ps1  in
         bind uu____66349
           (fun uu____66354  ->
              let uu____66355 = FStar_BigInt.of_int_fs n1  in ret uu____66355))
  
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
              let uu____66393 = env.FStar_TypeChecker_Env.universe_of env phi
                 in
              FStar_Syntax_Util.mk_squash uu____66393 phi  in
            let uu____66394 = new_uvar reason env typ  in
            bind uu____66394
              (fun uu____66409  ->
                 match uu____66409 with
                 | (uu____66416,ctx_uvar) ->
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
             (fun uu____66463  ->
                let uu____66464 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____66464)
             (fun uu____66469  ->
                let e1 =
                  let uu___1049_66471 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1049_66471.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1049_66471.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1049_66471.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1049_66471.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1049_66471.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1049_66471.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1049_66471.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1049_66471.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1049_66471.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1049_66471.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1049_66471.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1049_66471.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1049_66471.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1049_66471.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1049_66471.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1049_66471.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1049_66471.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1049_66471.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1049_66471.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1049_66471.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1049_66471.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1049_66471.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1049_66471.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1049_66471.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1049_66471.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1049_66471.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1049_66471.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1049_66471.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1049_66471.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1049_66471.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1049_66471.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1049_66471.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1049_66471.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1049_66471.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1049_66471.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1049_66471.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1049_66471.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1049_66471.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1049_66471.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1049_66471.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1049_66471.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1049_66471.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___1053_66483  ->
                     match () with
                     | () ->
                         let uu____66492 =
                           FStar_TypeChecker_TcTerm.type_of_tot_term e1 t  in
                         ret uu____66492) ()
                with
                | FStar_Errors.Err (uu____66519,msg) ->
                    let uu____66523 = tts e1 t  in
                    let uu____66525 =
                      let uu____66527 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____66527
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____66523 uu____66525 msg
                | FStar_Errors.Error (uu____66537,msg,uu____66539) ->
                    let uu____66542 = tts e1 t  in
                    let uu____66544 =
                      let uu____66546 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____66546
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____66542 uu____66544 msg))
  
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
             (fun uu____66599  ->
                let uu____66600 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc_ghost(%s)\n" uu____66600)
             (fun uu____66605  ->
                let e1 =
                  let uu___1070_66607 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1070_66607.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1070_66607.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1070_66607.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1070_66607.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1070_66607.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1070_66607.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1070_66607.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1070_66607.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1070_66607.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1070_66607.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1070_66607.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1070_66607.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1070_66607.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1070_66607.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1070_66607.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1070_66607.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1070_66607.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1070_66607.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1070_66607.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1070_66607.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1070_66607.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1070_66607.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1070_66607.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1070_66607.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1070_66607.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1070_66607.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1070_66607.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1070_66607.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1070_66607.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1070_66607.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1070_66607.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1070_66607.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1070_66607.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1070_66607.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1070_66607.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1070_66607.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1070_66607.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1070_66607.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1070_66607.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1070_66607.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1070_66607.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1070_66607.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___1074_66622  ->
                     match () with
                     | () ->
                         let uu____66631 =
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e1 t
                            in
                         (match uu____66631 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____66669,msg) ->
                    let uu____66673 = tts e1 t  in
                    let uu____66675 =
                      let uu____66677 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____66677
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____66673 uu____66675 msg
                | FStar_Errors.Error (uu____66687,msg,uu____66689) ->
                    let uu____66692 = tts e1 t  in
                    let uu____66694 =
                      let uu____66696 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____66696
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____66692 uu____66694 msg))
  
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
             (fun uu____66749  ->
                let uu____66750 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____66750)
             (fun uu____66756  ->
                let e1 =
                  let uu___1095_66758 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1095_66758.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1095_66758.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1095_66758.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1095_66758.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1095_66758.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1095_66758.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1095_66758.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1095_66758.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1095_66758.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1095_66758.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1095_66758.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1095_66758.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1095_66758.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1095_66758.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1095_66758.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1095_66758.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1095_66758.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1095_66758.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1095_66758.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1095_66758.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1095_66758.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1095_66758.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1095_66758.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1095_66758.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1095_66758.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1095_66758.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1095_66758.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1095_66758.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1095_66758.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1095_66758.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1095_66758.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1095_66758.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1095_66758.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1095_66758.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1095_66758.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1095_66758.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1095_66758.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1095_66758.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1095_66758.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1095_66758.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1095_66758.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1095_66758.FStar_TypeChecker_Env.nbe)
                  }  in
                let e2 =
                  let uu___1098_66761 = e1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1098_66761.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1098_66761.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1098_66761.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1098_66761.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1098_66761.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1098_66761.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1098_66761.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1098_66761.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1098_66761.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1098_66761.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1098_66761.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1098_66761.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1098_66761.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1098_66761.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1098_66761.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1098_66761.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1098_66761.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1098_66761.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1098_66761.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1098_66761.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1098_66761.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1098_66761.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1098_66761.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1098_66761.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___1098_66761.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1098_66761.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1098_66761.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1098_66761.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1098_66761.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1098_66761.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1098_66761.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1098_66761.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1098_66761.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1098_66761.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1098_66761.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1098_66761.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1098_66761.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1098_66761.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1098_66761.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1098_66761.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1098_66761.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1098_66761.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___1102_66776  ->
                     match () with
                     | () ->
                         let uu____66785 =
                           FStar_TypeChecker_TcTerm.tc_term e2 t  in
                         (match uu____66785 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____66823,msg) ->
                    let uu____66827 = tts e2 t  in
                    let uu____66829 =
                      let uu____66831 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____66831
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____66827 uu____66829 msg
                | FStar_Errors.Error (uu____66841,msg,uu____66843) ->
                    let uu____66846 = tts e2 t  in
                    let uu____66848 =
                      let uu____66850 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____66850
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____66846 uu____66848 msg))
  
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
  fun uu____66884  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___1127_66903 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___1127_66903.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___1127_66903.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___1127_66903.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___1127_66903.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___1127_66903.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___1127_66903.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___1127_66903.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___1127_66903.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___1127_66903.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___1127_66903.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___1127_66903.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___1127_66903.FStar_Tactics_Types.local_state)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____66928 = get_guard_policy ()  in
      bind uu____66928
        (fun old_pol  ->
           let uu____66934 = set_guard_policy pol  in
           bind uu____66934
             (fun uu____66938  ->
                bind t
                  (fun r  ->
                     let uu____66942 = set_guard_policy old_pol  in
                     bind uu____66942 (fun uu____66946  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____66950 = let uu____66955 = cur_goal ()  in trytac uu____66955  in
  bind uu____66950
    (fun uu___609_66962  ->
       match uu___609_66962 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____66968 = FStar_Options.peek ()  in ret uu____66968)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        mlog
          (fun uu____66993  ->
             let uu____66994 = FStar_TypeChecker_Rel.guard_to_string e g  in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason
               uu____66994)
          (fun uu____66999  ->
             let uu____67000 =
               add_implicits g.FStar_TypeChecker_Env.implicits  in
             bind uu____67000
               (fun uu____67004  ->
                  bind getopts
                    (fun opts  ->
                       let uu____67008 =
                         let uu____67009 =
                           FStar_TypeChecker_Rel.simplify_guard e g  in
                         uu____67009.FStar_TypeChecker_Env.guard_f  in
                       match uu____67008 with
                       | FStar_TypeChecker_Common.Trivial  -> ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____67013 = istrivial e f  in
                           if uu____67013
                           then ret ()
                           else
                             bind get
                               (fun ps  ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop  ->
                                      ((let uu____67026 =
                                          let uu____67032 =
                                            let uu____67034 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g
                                               in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____67034
                                             in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____67032)
                                           in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____67026);
                                       ret ())
                                  | FStar_Tactics_Types.Goal  ->
                                      mlog
                                        (fun uu____67040  ->
                                           let uu____67041 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____67041)
                                        (fun uu____67046  ->
                                           let uu____67047 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____67047
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___1156_67055 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___1156_67055.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___1156_67055.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___1156_67055.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___1156_67055.FStar_Tactics_Types.label)
                                                  }  in
                                                push_goals [goal1]))
                                  | FStar_Tactics_Types.SMT  ->
                                      mlog
                                        (fun uu____67059  ->
                                           let uu____67060 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____67060)
                                        (fun uu____67065  ->
                                           let uu____67066 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____67066
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___1163_67074 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___1163_67074.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___1163_67074.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___1163_67074.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___1163_67074.FStar_Tactics_Types.label)
                                                  }  in
                                                push_smt_goals [goal1]))
                                  | FStar_Tactics_Types.Force  ->
                                      mlog
                                        (fun uu____67078  ->
                                           let uu____67079 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____67079)
                                        (fun uu____67083  ->
                                           try
                                             (fun uu___1170_67088  ->
                                                match () with
                                                | () ->
                                                    let uu____67091 =
                                                      let uu____67093 =
                                                        let uu____67095 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____67095
                                                         in
                                                      Prims.op_Negation
                                                        uu____67093
                                                       in
                                                    if uu____67091
                                                    then
                                                      mlog
                                                        (fun uu____67102  ->
                                                           let uu____67103 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g
                                                              in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____67103)
                                                        (fun uu____67107  ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else ret ()) ()
                                           with
                                           | uu___1169_67112 ->
                                               mlog
                                                 (fun uu____67117  ->
                                                    let uu____67118 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g
                                                       in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____67118)
                                                 (fun uu____67122  ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____67134 =
      let uu____67137 = cur_goal ()  in
      bind uu____67137
        (fun goal  ->
           let uu____67143 =
             let uu____67152 = FStar_Tactics_Types.goal_env goal  in
             __tc_lax uu____67152 t  in
           bind uu____67143
             (fun uu____67163  ->
                match uu____67163 with
                | (uu____67172,typ,uu____67174) -> ret typ))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____67134
  
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
            let uu____67214 = mk_irrelevant_goal reason env phi opts label1
               in
            bind uu____67214 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____67226  ->
    let uu____67229 = cur_goal ()  in
    bind uu____67229
      (fun goal  ->
         let uu____67235 =
           let uu____67237 = FStar_Tactics_Types.goal_env goal  in
           let uu____67238 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____67237 uu____67238  in
         if uu____67235
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____67244 =
              let uu____67246 = FStar_Tactics_Types.goal_env goal  in
              let uu____67247 = FStar_Tactics_Types.goal_type goal  in
              tts uu____67246 uu____67247  in
            fail1 "Not a trivial goal: %s" uu____67244))
  
let divide : 'a 'b . FStar_BigInt.t -> 'a tac -> 'b tac -> ('a * 'b) tac =
  fun n1  ->
    fun l  ->
      fun r  ->
        bind get
          (fun p  ->
             let uu____67298 =
               try
                 (fun uu___1226_67321  ->
                    match () with
                    | () ->
                        let uu____67332 =
                          let uu____67341 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____67341
                            p.FStar_Tactics_Types.goals
                           in
                        ret uu____67332) ()
               with | uu___1225_67352 -> fail "divide: not enough goals"  in
             bind uu____67298
               (fun uu____67389  ->
                  match uu____67389 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___1208_67415 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___1208_67415.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___1208_67415.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___1208_67415.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___1208_67415.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___1208_67415.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___1208_67415.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___1208_67415.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___1208_67415.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___1208_67415.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___1208_67415.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___1208_67415.FStar_Tactics_Types.local_state)
                        }  in
                      let uu____67416 = set lp  in
                      bind uu____67416
                        (fun uu____67424  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___1214_67440 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___1214_67440.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___1214_67440.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___1214_67440.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___1214_67440.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___1214_67440.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___1214_67440.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___1214_67440.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___1214_67440.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___1214_67440.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___1214_67440.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___1214_67440.FStar_Tactics_Types.local_state)
                                       }  in
                                     let uu____67441 = set rp  in
                                     bind uu____67441
                                       (fun uu____67449  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___1220_67465 =
                                                        rp'  in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___1220_67465.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___1220_67465.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___1220_67465.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___1220_67465.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___1220_67465.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___1220_67465.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___1220_67465.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___1220_67465.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___1220_67465.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___1220_67465.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___1220_67465.FStar_Tactics_Types.local_state)
                                                      }  in
                                                    let uu____67466 = set p'
                                                       in
                                                    bind uu____67466
                                                      (fun uu____67474  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____67480 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____67502 = divide FStar_BigInt.one f idtac  in
    bind uu____67502
      (fun uu____67515  -> match uu____67515 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____67553::uu____67554 ->
             let uu____67557 =
               let uu____67566 = map tau  in
               divide FStar_BigInt.one tau uu____67566  in
             bind uu____67557
               (fun uu____67584  ->
                  match uu____67584 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____67626 =
        bind t1
          (fun uu____67631  ->
             let uu____67632 = map t2  in
             bind uu____67632 (fun uu____67640  -> ret ()))
         in
      focus uu____67626
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____67650  ->
    let uu____67653 =
      let uu____67656 = cur_goal ()  in
      bind uu____67656
        (fun goal  ->
           let uu____67665 =
             let uu____67672 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____67672  in
           match uu____67665 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____67681 =
                 let uu____67683 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____67683  in
               if uu____67681
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____67692 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____67692 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____67706 = new_uvar "intro" env' typ'  in
                  bind uu____67706
                    (fun uu____67723  ->
                       match uu____67723 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c))
                              in
                           let uu____67747 = set_solution goal sol  in
                           bind uu____67747
                             (fun uu____67753  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                    goal.FStar_Tactics_Types.label
                                   in
                                let uu____67755 =
                                  let uu____67758 = bnorm_goal g  in
                                  replace_cur uu____67758  in
                                bind uu____67755 (fun uu____67760  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____67765 =
                 let uu____67767 = FStar_Tactics_Types.goal_env goal  in
                 let uu____67768 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____67767 uu____67768  in
               fail1 "goal is not an arrow (%s)" uu____67765)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____67653
  
let (intro_rec :
  unit -> (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder) tac) =
  fun uu____67786  ->
    let uu____67793 = cur_goal ()  in
    bind uu____67793
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____67812 =
            let uu____67819 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____67819  in
          match uu____67812 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____67832 =
                let uu____67834 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____67834  in
              if uu____67832
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____67851 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____67851
                    in
                 let bs =
                   let uu____67862 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____67862; b]  in
                 let env' =
                   let uu____67888 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____67888 bs  in
                 let uu____67889 =
                   let uu____67896 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____67896  in
                 bind uu____67889
                   (fun uu____67916  ->
                      match uu____67916 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____67930 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____67933 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____67930
                              FStar_Parser_Const.effect_Tot_lid uu____67933
                              [] FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____67951 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____67951 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____67973 =
                                   let uu____67974 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____67974.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____67973
                                  in
                               let uu____67990 = set_solution goal tm  in
                               bind uu____67990
                                 (fun uu____67999  ->
                                    let uu____68000 =
                                      let uu____68003 =
                                        bnorm_goal
                                          (let uu___1291_68006 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___1291_68006.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___1291_68006.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___1291_68006.FStar_Tactics_Types.is_guard);
                                             FStar_Tactics_Types.label =
                                               (uu___1291_68006.FStar_Tactics_Types.label)
                                           })
                                         in
                                      replace_cur uu____68003  in
                                    bind uu____68000
                                      (fun uu____68013  ->
                                         let uu____68014 =
                                           let uu____68019 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____68019, b)  in
                                         ret uu____68014)))))
          | FStar_Pervasives_Native.None  ->
              let uu____68028 =
                let uu____68030 = FStar_Tactics_Types.goal_env goal  in
                let uu____68031 = FStar_Tactics_Types.goal_type goal  in
                tts uu____68030 uu____68031  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____68028))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____68051 = cur_goal ()  in
    bind uu____68051
      (fun goal  ->
         mlog
           (fun uu____68058  ->
              let uu____68059 =
                let uu____68061 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____68061  in
              FStar_Util.print1 "norm: witness = %s\n" uu____68059)
           (fun uu____68067  ->
              let steps =
                let uu____68071 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____68071
                 in
              let t =
                let uu____68075 = FStar_Tactics_Types.goal_env goal  in
                let uu____68076 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____68075 uu____68076  in
              let uu____68077 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____68077))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____68102 =
          bind get
            (fun ps  ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
                 | g::uu____68110 -> g.FStar_Tactics_Types.opts
                 | uu____68113 -> FStar_Options.peek ()  in
               mlog
                 (fun uu____68118  ->
                    let uu____68119 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____68119)
                 (fun uu____68124  ->
                    let uu____68125 = __tc_lax e t  in
                    bind uu____68125
                      (fun uu____68146  ->
                         match uu____68146 with
                         | (t1,uu____68156,uu____68157) ->
                             let steps =
                               let uu____68161 =
                                 FStar_TypeChecker_Normalize.tr_norm_steps s
                                  in
                               FStar_List.append
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu____68161
                                in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1
                                in
                             mlog
                               (fun uu____68167  ->
                                  let uu____68168 =
                                    FStar_Syntax_Print.term_to_string t2  in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____68168)
                               (fun uu____68172  -> ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____68102
  
let (refine_intro : unit -> unit tac) =
  fun uu____68185  ->
    let uu____68188 =
      let uu____68191 = cur_goal ()  in
      bind uu____68191
        (fun g  ->
           let uu____68198 =
             let uu____68209 = FStar_Tactics_Types.goal_env g  in
             let uu____68210 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____68209
               uu____68210
              in
           match uu____68198 with
           | (uu____68213,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____68239 =
                 let uu____68244 =
                   let uu____68249 =
                     let uu____68250 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____68250]  in
                   FStar_Syntax_Subst.open_term uu____68249 phi  in
                 match uu____68244 with
                 | (bvs,phi1) ->
                     let uu____68275 =
                       let uu____68276 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____68276  in
                     (uu____68275, phi1)
                  in
               (match uu____68239 with
                | (bv1,phi1) ->
                    let uu____68295 =
                      let uu____68298 = FStar_Tactics_Types.goal_env g  in
                      let uu____68299 =
                        let uu____68300 =
                          let uu____68303 =
                            let uu____68304 =
                              let uu____68311 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____68311)  in
                            FStar_Syntax_Syntax.NT uu____68304  in
                          [uu____68303]  in
                        FStar_Syntax_Subst.subst uu____68300 phi1  in
                      mk_irrelevant_goal "refine_intro refinement"
                        uu____68298 uu____68299 g.FStar_Tactics_Types.opts
                        g.FStar_Tactics_Types.label
                       in
                    bind uu____68295
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____68320  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____68188
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____68343 = cur_goal ()  in
      bind uu____68343
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____68352 = FStar_Tactics_Types.goal_env goal  in
               let uu____68353 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____68352 uu____68353
             else FStar_Tactics_Types.goal_env goal  in
           let uu____68356 = __tc env t  in
           bind uu____68356
             (fun uu____68375  ->
                match uu____68375 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____68390  ->
                         let uu____68391 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____68393 =
                           let uu____68395 =
                             FStar_Tactics_Types.goal_env goal  in
                           FStar_TypeChecker_Rel.guard_to_string uu____68395
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____68391 uu____68393)
                      (fun uu____68399  ->
                         let uu____68400 =
                           let uu____68403 =
                             FStar_Tactics_Types.goal_env goal  in
                           proc_guard "__exact typing" uu____68403 guard  in
                         bind uu____68400
                           (fun uu____68406  ->
                              mlog
                                (fun uu____68410  ->
                                   let uu____68411 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____68413 =
                                     let uu____68415 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____68415
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____68411 uu____68413)
                                (fun uu____68419  ->
                                   let uu____68420 =
                                     let uu____68424 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____68425 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____68424 typ uu____68425  in
                                   bind uu____68420
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____68435 =
                                             let uu____68437 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____68437 t1  in
                                           let uu____68438 =
                                             let uu____68440 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____68440 typ  in
                                           let uu____68441 =
                                             let uu____68443 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____68444 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____68443 uu____68444  in
                                           let uu____68445 =
                                             let uu____68447 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____68448 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____68447 uu____68448  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____68435 uu____68438
                                             uu____68441 uu____68445)))))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun try_refine  ->
    fun set_expected_typ1  ->
      fun tm  ->
        let uu____68474 =
          mlog
            (fun uu____68479  ->
               let uu____68480 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____68480)
            (fun uu____68485  ->
               let uu____68486 =
                 let uu____68493 = __exact_now set_expected_typ1 tm  in
                 catch uu____68493  in
               bind uu____68486
                 (fun uu___611_68502  ->
                    match uu___611_68502 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        traise e
                    | FStar_Util.Inl e ->
                        mlog
                          (fun uu____68513  ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____68517  ->
                             let uu____68518 =
                               let uu____68525 =
                                 let uu____68528 =
                                   norm [FStar_Syntax_Embeddings.Delta]  in
                                 bind uu____68528
                                   (fun uu____68533  ->
                                      let uu____68534 = refine_intro ()  in
                                      bind uu____68534
                                        (fun uu____68538  ->
                                           __exact_now set_expected_typ1 tm))
                                  in
                               catch uu____68525  in
                             bind uu____68518
                               (fun uu___610_68545  ->
                                  match uu___610_68545 with
                                  | FStar_Util.Inr r ->
                                      mlog
                                        (fun uu____68554  ->
                                           FStar_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu____68557  -> ret ())
                                  | FStar_Util.Inl uu____68558 ->
                                      mlog
                                        (fun uu____68560  ->
                                           FStar_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu____68563  -> traise e)))))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____68474
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____68615 = f x  in
          bind uu____68615
            (fun y  ->
               let uu____68623 = mapM f xs  in
               bind uu____68623 (fun ys  -> ret (y :: ys)))
  
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
          let uu____68695 = do_unify e ty1 ty2  in
          bind uu____68695
            (fun uu___612_68709  ->
               if uu___612_68709
               then ret acc
               else
                 (let uu____68729 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____68729 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____68750 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____68752 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____68750
                        uu____68752
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____68769 =
                        let uu____68771 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____68771  in
                      if uu____68769
                      then fail "Codomain is effectful"
                      else
                        (let uu____68795 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____68795
                           (fun uu____68822  ->
                              match uu____68822 with
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
      let uu____68912 =
        mlog
          (fun uu____68917  ->
             let uu____68918 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_apply: tm = %s\n" uu____68918)
          (fun uu____68923  ->
             let uu____68924 = cur_goal ()  in
             bind uu____68924
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____68932 = __tc e tm  in
                  bind uu____68932
                    (fun uu____68953  ->
                       match uu____68953 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____68966 =
                             let uu____68977 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____68977  in
                           bind uu____68966
                             (fun uvs  ->
                                let fix_qual q =
                                  match q with
                                  | FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Meta uu____69015)
                                      ->
                                      FStar_Pervasives_Native.Some
                                        (FStar_Syntax_Syntax.Implicit false)
                                  | uu____69019 -> q  in
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____69042  ->
                                       fun w  ->
                                         match uu____69042 with
                                         | (uvt,q,uu____69060) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, (fix_qual q))]) uvs tm1
                                   in
                                let uvset =
                                  let uu____69092 =
                                    FStar_Syntax_Free.new_uv_set ()  in
                                  FStar_List.fold_right
                                    (fun uu____69109  ->
                                       fun s  ->
                                         match uu____69109 with
                                         | (uu____69121,uu____69122,uv) ->
                                             let uu____69124 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                in
                                             FStar_Util.set_union s
                                               uu____69124) uvs uu____69092
                                   in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset  in
                                let uu____69134 = solve' goal w  in
                                bind uu____69134
                                  (fun uu____69139  ->
                                     let uu____69140 =
                                       mapM
                                         (fun uu____69157  ->
                                            match uu____69157 with
                                            | (uvt,q,uv) ->
                                                let uu____69169 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                   in
                                                (match uu____69169 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____69174 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____69175 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv)
                                                        in
                                                     if uu____69175
                                                     then ret ()
                                                     else
                                                       (let uu____69182 =
                                                          let uu____69185 =
                                                            bnorm_goal
                                                              (let uu___1452_69188
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___1452_69188.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___1452_69188.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false;
                                                                 FStar_Tactics_Types.label
                                                                   =
                                                                   (uu___1452_69188.FStar_Tactics_Types.label)
                                                               })
                                                             in
                                                          [uu____69185]  in
                                                        add_goals uu____69182)))
                                         uvs
                                        in
                                     bind uu____69140
                                       (fun uu____69193  ->
                                          proc_guard "apply guard" e guard))))))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____68912
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____69221 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____69221
    then
      let uu____69230 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____69245 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____69298 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____69230 with
      | (pre,post) ->
          let post1 =
            let uu____69331 =
              let uu____69342 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____69342]  in
            FStar_Syntax_Util.mk_app post uu____69331  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____69373 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____69373
       then
         let uu____69382 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____69382
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
            let uu____69461 = f x e  in
            bind uu____69461 (fun e'  -> fold_left f e' xs1)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____69476 =
      let uu____69479 =
        bind get
          (fun ps  ->
             mlog
               (fun uu____69486  ->
                  let uu____69487 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____69487)
               (fun uu____69493  ->
                  let is_unit_t t =
                    let uu____69501 =
                      let uu____69502 = FStar_Syntax_Subst.compress t  in
                      uu____69502.FStar_Syntax_Syntax.n  in
                    match uu____69501 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____69508 -> false  in
                  let uu____69510 = cur_goal ()  in
                  bind uu____69510
                    (fun goal  ->
                       let uu____69516 =
                         let uu____69525 = FStar_Tactics_Types.goal_env goal
                            in
                         __tc uu____69525 tm  in
                       bind uu____69516
                         (fun uu____69540  ->
                            match uu____69540 with
                            | (tm1,t,guard) ->
                                let uu____69552 =
                                  FStar_Syntax_Util.arrow_formals_comp t  in
                                (match uu____69552 with
                                 | (bs,comp) ->
                                     let uu____69585 = lemma_or_sq comp  in
                                     (match uu____69585 with
                                      | FStar_Pervasives_Native.None  ->
                                          fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre,post) ->
                                          let uu____69605 =
                                            fold_left
                                              (fun uu____69667  ->
                                                 fun uu____69668  ->
                                                   match (uu____69667,
                                                           uu____69668)
                                                   with
                                                   | ((b,aq),(uvs,imps,subst1))
                                                       ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst1
                                                           b.FStar_Syntax_Syntax.sort
                                                          in
                                                       let uu____69819 =
                                                         is_unit_t b_t  in
                                                       if uu____69819
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
                                                         (let uu____69942 =
                                                            let uu____69949 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            new_uvar
                                                              "apply_lemma"
                                                              uu____69949 b_t
                                                             in
                                                          bind uu____69942
                                                            (fun uu____69980 
                                                               ->
                                                               match uu____69980
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
                                          bind uu____69605
                                            (fun uu____70166  ->
                                               match uu____70166 with
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
                                                   let uu____70254 =
                                                     let uu____70258 =
                                                       FStar_Tactics_Types.goal_env
                                                         goal
                                                        in
                                                     let uu____70259 =
                                                       FStar_Syntax_Util.mk_squash
                                                         FStar_Syntax_Syntax.U_zero
                                                         post1
                                                        in
                                                     let uu____70260 =
                                                       FStar_Tactics_Types.goal_type
                                                         goal
                                                        in
                                                     do_unify uu____70258
                                                       uu____70259
                                                       uu____70260
                                                      in
                                                   bind uu____70254
                                                     (fun b  ->
                                                        if
                                                          Prims.op_Negation b
                                                        then
                                                          let uu____70271 =
                                                            let uu____70273 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            tts uu____70273
                                                              tm1
                                                             in
                                                          let uu____70274 =
                                                            let uu____70276 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            let uu____70277 =
                                                              FStar_Syntax_Util.mk_squash
                                                                FStar_Syntax_Syntax.U_zero
                                                                post1
                                                               in
                                                            tts uu____70276
                                                              uu____70277
                                                             in
                                                          let uu____70278 =
                                                            let uu____70280 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            let uu____70281 =
                                                              FStar_Tactics_Types.goal_type
                                                                goal
                                                               in
                                                            tts uu____70280
                                                              uu____70281
                                                             in
                                                          fail3
                                                            "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                            uu____70271
                                                            uu____70274
                                                            uu____70278
                                                        else
                                                          (let uu____70285 =
                                                             solve' goal
                                                               FStar_Syntax_Util.exp_unit
                                                              in
                                                           bind uu____70285
                                                             (fun uu____70293
                                                                 ->
                                                                let is_free_uvar
                                                                  uv t1 =
                                                                  let free_uvars
                                                                    =
                                                                    let uu____70319
                                                                    =
                                                                    let uu____70322
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____70322
                                                                     in
                                                                    FStar_List.map
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____70319
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
                                                                    let uu____70358
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____70358)
                                                                    goals
                                                                   in
                                                                let checkone
                                                                  t1 goals =
                                                                  let uu____70375
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                  match uu____70375
                                                                  with
                                                                  | (hd1,uu____70394)
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____70421)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____70438
                                                                    -> false)
                                                                   in
                                                                let uu____70440
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
                                                                    let uu____70483
                                                                    = imp  in
                                                                    match uu____70483
                                                                    with
                                                                    | 
                                                                    (term,ctx_uvar)
                                                                    ->
                                                                    let uu____70494
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____70494
                                                                    with
                                                                    | 
                                                                    (hd1,uu____70516)
                                                                    ->
                                                                    let uu____70541
                                                                    =
                                                                    let uu____70542
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____70542.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____70541
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____70550)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___1562_70570
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___1562_70570.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___1562_70570.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___1562_70570.FStar_Tactics_Types.is_guard);
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___1562_70570.FStar_Tactics_Types.label)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____70573
                                                                    ->
                                                                    mlog
                                                                    (fun
                                                                    uu____70579
                                                                     ->
                                                                    let uu____70580
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                                                     in
                                                                    let uu____70582
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____70580
                                                                    uu____70582)
                                                                    (fun
                                                                    uu____70589
                                                                     ->
                                                                    let env =
                                                                    let uu___1567_70591
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___1567_70591.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1567_70591.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1567_70591.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___1567_70591.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1567_70591.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1567_70591.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1567_70591.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1567_70591.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___1567_70591.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___1567_70591.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___1567_70591.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1567_70591.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1567_70591.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1567_70591.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1567_70591.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1567_70591.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1567_70591.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1567_70591.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___1567_70591.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___1567_70591.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___1567_70591.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1567_70591.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1567_70591.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1567_70591.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1567_70591.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1567_70591.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1567_70591.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1567_70591.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1567_70591.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1567_70591.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1567_70591.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1567_70591.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1567_70591.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1567_70591.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___1567_70591.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1567_70591.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1567_70591.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___1567_70591.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1567_70591.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1567_70591.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1567_70591.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1567_70591.FStar_TypeChecker_Env.nbe)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let uu____70594
                                                                    =
                                                                    let uu____70597
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____70601
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
                                                                    let uu____70603
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____70601
                                                                    uu____70603
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____70609
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    uu____70597
                                                                    uu____70609
                                                                    g_typ  in
                                                                    bind
                                                                    uu____70594
                                                                    (fun
                                                                    uu____70613
                                                                     ->
                                                                    ret []))))))
                                                                   in
                                                                bind
                                                                  uu____70440
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
                                                                    let uu____70677
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____70677
                                                                    then
                                                                    let uu____70682
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____70682
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
                                                                    let uu____70697
                                                                    =
                                                                    let uu____70699
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____70699
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____70697)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____70700
                                                                    =
                                                                    let uu____70703
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____70703
                                                                    guard  in
                                                                    bind
                                                                    uu____70700
                                                                    (fun
                                                                    uu____70707
                                                                     ->
                                                                    let uu____70708
                                                                    =
                                                                    let uu____70711
                                                                    =
                                                                    let uu____70713
                                                                    =
                                                                    let uu____70715
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____70716
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____70715
                                                                    uu____70716
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____70713
                                                                     in
                                                                    if
                                                                    uu____70711
                                                                    then
                                                                    let uu____70720
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____70720
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    goal.FStar_Tactics_Types.label
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____70708
                                                                    (fun
                                                                    uu____70725
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2)))))))))))))
         in
      focus uu____69479  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____69476
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____70749 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____70749 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____70759::(e1,uu____70761)::(e2,uu____70763)::[])) when
        (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) ||
          (FStar_Ident.lid_equals l FStar_Parser_Const.c_eq2_lid)
        -> FStar_Pervasives_Native.Some (e1, e2)
    | uu____70824 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____70849 = destruct_eq' typ  in
    match uu____70849 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____70879 = FStar_Syntax_Util.un_squash typ  in
        (match uu____70879 with
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
        let uu____70948 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____70948 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', bv', [])
            else
              (let uu____71006 = aux e'  in
               FStar_Util.map_opt uu____71006
                 (fun uu____71037  ->
                    match uu____71037 with
                    | (e'',bv,bvs) -> (e'', bv, (bv' :: bvs))))
         in
      let uu____71063 = aux e  in
      FStar_Util.map_opt uu____71063
        (fun uu____71094  ->
           match uu____71094 with
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
          let uu____71168 =
            let uu____71179 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____71179  in
          FStar_Util.map_opt uu____71168
            (fun uu____71197  ->
               match uu____71197 with
               | (e0,b11,bvs) ->
                   let s1 bv =
                     let uu___1640_71219 = bv  in
                     let uu____71220 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___1640_71219.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___1640_71219.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____71220
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___1644_71228 =
                       g.FStar_Tactics_Types.goal_ctx_uvar  in
                     let uu____71229 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____71238 =
                       let uu____71241 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____71241  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___1644_71228.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____71229;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____71238;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___1644_71228.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___1644_71228.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___1644_71228.FStar_Syntax_Syntax.ctx_uvar_range);
                       FStar_Syntax_Syntax.ctx_uvar_meta =
                         (uu___1644_71228.FStar_Syntax_Syntax.ctx_uvar_meta)
                     }  in
                   let uu___1647_71242 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1647_71242.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___1647_71242.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___1647_71242.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1647_71242.FStar_Tactics_Types.label)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____71253 =
      let uu____71256 = cur_goal ()  in
      bind uu____71256
        (fun goal  ->
           let uu____71264 = h  in
           match uu____71264 with
           | (bv,uu____71268) ->
               mlog
                 (fun uu____71276  ->
                    let uu____71277 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____71279 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____71277
                      uu____71279)
                 (fun uu____71284  ->
                    let uu____71285 =
                      let uu____71296 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____71296  in
                    match uu____71285 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                        let uu____71323 =
                          destruct_eq bv1.FStar_Syntax_Syntax.sort  in
                        (match uu____71323 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____71338 =
                               let uu____71339 =
                                 FStar_Syntax_Subst.compress x  in
                               uu____71339.FStar_Syntax_Syntax.n  in
                             (match uu____71338 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv2 =
                                    let uu___1670_71356 = bv2  in
                                    let uu____71357 =
                                      FStar_Syntax_Subst.subst s
                                        bv2.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1670_71356.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1670_71356.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____71357
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv1 :: bvs1)  in
                                  let new_goal =
                                    let uu___1674_71365 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____71366 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____71375 =
                                      let uu____71378 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____71378
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___1674_71365.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____71366;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____71375;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___1674_71365.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___1674_71365.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___1674_71365.FStar_Syntax_Syntax.ctx_uvar_range);
                                      FStar_Syntax_Syntax.ctx_uvar_meta =
                                        (uu___1674_71365.FStar_Syntax_Syntax.ctx_uvar_meta)
                                    }  in
                                  replace_cur
                                    (let uu___1677_71381 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___1677_71381.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___1677_71381.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___1677_71381.FStar_Tactics_Types.is_guard);
                                       FStar_Tactics_Types.label =
                                         (uu___1677_71381.FStar_Tactics_Types.label)
                                     })
                              | uu____71382 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____71384 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____71253
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____71414 =
        let uu____71417 = cur_goal ()  in
        bind uu____71417
          (fun goal  ->
             let uu____71428 = b  in
             match uu____71428 with
             | (bv,uu____71432) ->
                 let bv' =
                   let uu____71438 =
                     let uu___1688_71439 = bv  in
                     let uu____71440 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____71440;
                       FStar_Syntax_Syntax.index =
                         (uu___1688_71439.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___1688_71439.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____71438  in
                 let s1 =
                   let uu____71445 =
                     let uu____71446 =
                       let uu____71453 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____71453)  in
                     FStar_Syntax_Syntax.NT uu____71446  in
                   [uu____71445]  in
                 let uu____71458 = subst_goal bv bv' s1 goal  in
                 (match uu____71458 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____71414
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____71480 =
      let uu____71483 = cur_goal ()  in
      bind uu____71483
        (fun goal  ->
           let uu____71492 = b  in
           match uu____71492 with
           | (bv,uu____71496) ->
               let uu____71501 =
                 let uu____71512 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____71512  in
               (match uu____71501 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                    let uu____71539 = FStar_Syntax_Util.type_u ()  in
                    (match uu____71539 with
                     | (ty,u) ->
                         let uu____71548 = new_uvar "binder_retype" e0 ty  in
                         bind uu____71548
                           (fun uu____71567  ->
                              match uu____71567 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___1712_71577 = bv1  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1712_71577.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1712_71577.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____71581 =
                                      let uu____71582 =
                                        let uu____71589 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv1, uu____71589)  in
                                      FStar_Syntax_Syntax.NT uu____71582  in
                                    [uu____71581]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___1717_71601 = b1  in
                                         let uu____71602 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___1717_71601.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___1717_71601.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____71602
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____71609  ->
                                       let new_goal =
                                         let uu____71611 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____71612 =
                                           let uu____71613 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____71613
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____71611 uu____71612
                                          in
                                       let uu____71614 = add_goals [new_goal]
                                          in
                                       bind uu____71614
                                         (fun uu____71619  ->
                                            let uu____71620 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv1.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____71620
                                              goal.FStar_Tactics_Types.opts
                                              goal.FStar_Tactics_Types.label))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____71480
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____71646 =
        let uu____71649 = cur_goal ()  in
        bind uu____71649
          (fun goal  ->
             let uu____71658 = b  in
             match uu____71658 with
             | (bv,uu____71662) ->
                 let uu____71667 =
                   let uu____71678 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____71678  in
                 (match uu____71667 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                      let steps =
                        let uu____71708 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____71708
                         in
                      let sort' =
                        normalize steps e0 bv1.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___1738_71713 = bv1  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___1738_71713.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___1738_71713.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____71715 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____71715))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____71646
  
let (revert : unit -> unit tac) =
  fun uu____71728  ->
    let uu____71731 = cur_goal ()  in
    bind uu____71731
      (fun goal  ->
         let uu____71737 =
           let uu____71744 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____71744  in
         match uu____71737 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____71761 =
                 let uu____71764 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____71764  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____71761
                in
             let uu____71779 = new_uvar "revert" env' typ'  in
             bind uu____71779
               (fun uu____71795  ->
                  match uu____71795 with
                  | (r,u_r) ->
                      let uu____71804 =
                        let uu____71807 =
                          let uu____71808 =
                            let uu____71809 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____71809.FStar_Syntax_Syntax.pos  in
                          let uu____71812 =
                            let uu____71817 =
                              let uu____71818 =
                                let uu____71827 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____71827  in
                              [uu____71818]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____71817  in
                          uu____71812 FStar_Pervasives_Native.None
                            uu____71808
                           in
                        set_solution goal uu____71807  in
                      bind uu____71804
                        (fun uu____71846  ->
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
      let uu____71860 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____71860
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____71876 = cur_goal ()  in
    bind uu____71876
      (fun goal  ->
         mlog
           (fun uu____71884  ->
              let uu____71885 = FStar_Syntax_Print.binder_to_string b  in
              let uu____71887 =
                let uu____71889 =
                  let uu____71891 =
                    let uu____71900 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____71900  in
                  FStar_All.pipe_right uu____71891 FStar_List.length  in
                FStar_All.pipe_right uu____71889 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____71885 uu____71887)
           (fun uu____71921  ->
              let uu____71922 =
                let uu____71933 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____71933  in
              match uu____71922 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bv1,bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____71978 =
                          free_in bv1 bv'.FStar_Syntax_Syntax.sort  in
                        if uu____71978
                        then
                          let uu____71983 =
                            let uu____71985 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____71985
                             in
                          fail uu____71983
                        else check1 bvs2
                     in
                  let uu____71990 =
                    let uu____71992 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv1 uu____71992  in
                  if uu____71990
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____71999 = check1 bvs  in
                     bind uu____71999
                       (fun uu____72005  ->
                          let env' = push_bvs e' bvs  in
                          let uu____72007 =
                            let uu____72014 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____72014  in
                          bind uu____72007
                            (fun uu____72024  ->
                               match uu____72024 with
                               | (ut,uvar_ut) ->
                                   let uu____72033 = set_solution goal ut  in
                                   bind uu____72033
                                     (fun uu____72038  ->
                                        let uu____72039 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                            goal.FStar_Tactics_Types.label
                                           in
                                        replace_cur uu____72039))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____72047  ->
    let uu____72050 = cur_goal ()  in
    bind uu____72050
      (fun goal  ->
         let uu____72056 =
           let uu____72063 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____72063  in
         match uu____72056 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____72072) ->
             let uu____72077 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____72077)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____72090 = cur_goal ()  in
    bind uu____72090
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____72100 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____72100  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____72103  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____72116 = cur_goal ()  in
    bind uu____72116
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____72126 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____72126  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____72129  -> add_goals [g']))
  
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
            let uu____72170 = FStar_Syntax_Subst.compress t  in
            uu____72170.FStar_Syntax_Syntax.n  in
          let uu____72173 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___1922_72180 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___1922_72180.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___1922_72180.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____72173
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____72197 =
                   let uu____72198 = FStar_Syntax_Subst.compress t1  in
                   uu____72198.FStar_Syntax_Syntax.n  in
                 match uu____72197 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____72229 = ff hd1  in
                     bind uu____72229
                       (fun hd2  ->
                          let fa uu____72255 =
                            match uu____72255 with
                            | (a,q) ->
                                let uu____72276 = ff a  in
                                bind uu____72276 (fun a1  -> ret (a1, q))
                             in
                          let uu____72295 = mapM fa args  in
                          bind uu____72295
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____72377 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____72377 with
                      | (bs1,t') ->
                          let uu____72386 =
                            let uu____72389 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____72389 t'  in
                          bind uu____72386
                            (fun t''  ->
                               let uu____72393 =
                                 let uu____72394 =
                                   let uu____72413 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____72422 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____72413, uu____72422, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____72394  in
                               ret uu____72393))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____72497 = ff hd1  in
                     bind uu____72497
                       (fun hd2  ->
                          let ffb br =
                            let uu____72512 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____72512 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____72544 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____72544  in
                                let uu____72545 = ff1 e  in
                                bind uu____72545
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____72560 = mapM ffb brs  in
                          bind uu____72560
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____72604;
                          FStar_Syntax_Syntax.lbtyp = uu____72605;
                          FStar_Syntax_Syntax.lbeff = uu____72606;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____72608;
                          FStar_Syntax_Syntax.lbpos = uu____72609;_}::[]),e)
                     ->
                     let lb =
                       let uu____72637 =
                         let uu____72638 = FStar_Syntax_Subst.compress t1  in
                         uu____72638.FStar_Syntax_Syntax.n  in
                       match uu____72637 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____72642) -> lb
                       | uu____72658 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____72668 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____72668
                         (fun def1  ->
                            ret
                              (let uu___1875_72674 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1875_72674.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1875_72674.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1875_72674.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1875_72674.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1875_72674.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1875_72674.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____72675 = fflb lb  in
                     bind uu____72675
                       (fun lb1  ->
                          let uu____72685 =
                            let uu____72690 =
                              let uu____72691 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____72691]  in
                            FStar_Syntax_Subst.open_term uu____72690 e  in
                          match uu____72685 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____72721 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____72721  in
                              let uu____72722 = ff1 e1  in
                              bind uu____72722
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____72769 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____72769
                         (fun def  ->
                            ret
                              (let uu___1893_72775 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1893_72775.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1893_72775.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1893_72775.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1893_72775.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1893_72775.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1893_72775.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____72776 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____72776 with
                      | (lbs1,e1) ->
                          let uu____72791 = mapM fflb lbs1  in
                          bind uu____72791
                            (fun lbs2  ->
                               let uu____72803 = ff e1  in
                               bind uu____72803
                                 (fun e2  ->
                                    let uu____72811 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____72811 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____72882 = ff t2  in
                     bind uu____72882
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____72913 = ff t2  in
                     bind uu____72913
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____72920 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___1917_72927 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___1917_72927.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___1917_72927.FStar_Syntax_Syntax.vars)
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
              let uu____72974 =
                FStar_TypeChecker_TcTerm.tc_term
                  (let uu___1930_72983 = env  in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___1930_72983.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___1930_72983.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___1930_72983.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___1930_72983.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_sig =
                       (uu___1930_72983.FStar_TypeChecker_Env.gamma_sig);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___1930_72983.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___1930_72983.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___1930_72983.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___1930_72983.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.attrtab =
                       (uu___1930_72983.FStar_TypeChecker_Env.attrtab);
                     FStar_TypeChecker_Env.is_pattern =
                       (uu___1930_72983.FStar_TypeChecker_Env.is_pattern);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___1930_72983.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___1930_72983.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___1930_72983.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___1930_72983.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___1930_72983.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___1930_72983.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___1930_72983.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___1930_72983.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___1930_72983.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax = true;
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___1930_72983.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.phase1 =
                       (uu___1930_72983.FStar_TypeChecker_Env.phase1);
                     FStar_TypeChecker_Env.failhard =
                       (uu___1930_72983.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___1930_72983.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.uvar_subtyping =
                       (uu___1930_72983.FStar_TypeChecker_Env.uvar_subtyping);
                     FStar_TypeChecker_Env.tc_term =
                       (uu___1930_72983.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.type_of =
                       (uu___1930_72983.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___1930_72983.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.check_type_of =
                       (uu___1930_72983.FStar_TypeChecker_Env.check_type_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___1930_72983.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (uu___1930_72983.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (uu___1930_72983.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.fv_delta_depths =
                       (uu___1930_72983.FStar_TypeChecker_Env.fv_delta_depths);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___1930_72983.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (uu___1930_72983.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.splice =
                       (uu___1930_72983.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.postprocess =
                       (uu___1930_72983.FStar_TypeChecker_Env.postprocess);
                     FStar_TypeChecker_Env.is_native_tactic =
                       (uu___1930_72983.FStar_TypeChecker_Env.is_native_tactic);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___1930_72983.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (uu___1930_72983.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (uu___1930_72983.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.nbe =
                       (uu___1930_72983.FStar_TypeChecker_Env.nbe)
                   }) t
                 in
              match uu____72974 with
              | (t1,lcomp,g) ->
                  let uu____72990 =
                    (let uu____72994 =
                       FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                     Prims.op_Negation uu____72994) ||
                      (let uu____72997 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____72997)
                     in
                  if uu____72990
                  then ret t1
                  else
                    (let rewrite_eq =
                       let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                       let uu____73008 = new_uvar "pointwise_rec" env typ  in
                       bind uu____73008
                         (fun uu____73025  ->
                            match uu____73025 with
                            | (ut,uvar_ut) ->
                                (log ps
                                   (fun uu____73038  ->
                                      let uu____73039 =
                                        FStar_Syntax_Print.term_to_string t1
                                         in
                                      let uu____73041 =
                                        FStar_Syntax_Print.term_to_string ut
                                         in
                                      FStar_Util.print2
                                        "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                        uu____73039 uu____73041);
                                 (let uu____73044 =
                                    let uu____73047 =
                                      let uu____73048 =
                                        FStar_TypeChecker_TcTerm.universe_of
                                          env typ
                                         in
                                      FStar_Syntax_Util.mk_eq2 uu____73048
                                        typ t1 ut
                                       in
                                    add_irrelevant_goal
                                      "pointwise_rec equation" env
                                      uu____73047 opts label1
                                     in
                                  bind uu____73044
                                    (fun uu____73052  ->
                                       let uu____73053 =
                                         bind tau
                                           (fun uu____73059  ->
                                              let ut1 =
                                                FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                  env ut
                                                 in
                                              log ps
                                                (fun uu____73065  ->
                                                   let uu____73066 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1
                                                      in
                                                   let uu____73068 =
                                                     FStar_Syntax_Print.term_to_string
                                                       ut1
                                                      in
                                                   FStar_Util.print2
                                                     "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                     uu____73066 uu____73068);
                                              ret ut1)
                                          in
                                       focus uu____73053))))
                        in
                     let uu____73071 = catch rewrite_eq  in
                     bind uu____73071
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
          let uu____73283 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____73283
            (fun t1  ->
               let uu____73291 =
                 f env
                   (let uu___2007_73299 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___2007_73299.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___2007_73299.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____73291
                 (fun uu____73315  ->
                    match uu____73315 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____73338 =
                               let uu____73339 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____73339.FStar_Syntax_Syntax.n  in
                             match uu____73338 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____73376 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____73376
                                   (fun uu____73398  ->
                                      match uu____73398 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____73414 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____73414
                                            (fun uu____73438  ->
                                               match uu____73438 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___1987_73468 =
                                                         t3  in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___1987_73468.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___1987_73468.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____73510 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____73510 with
                                  | (bs1,t') ->
                                      let uu____73525 =
                                        let uu____73532 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____73532 ctrl1 t'
                                         in
                                      bind uu____73525
                                        (fun uu____73547  ->
                                           match uu____73547 with
                                           | (t'',ctrl2) ->
                                               let uu____73562 =
                                                 let uu____73569 =
                                                   let uu___2000_73572 = t4
                                                      in
                                                   let uu____73575 =
                                                     let uu____73576 =
                                                       let uu____73595 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____73604 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____73595,
                                                         uu____73604, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____73576
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____73575;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___2000_73572.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___2000_73572.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____73569, ctrl2)  in
                                               ret uu____73562))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____73657 -> ret (t3, ctrl1))))

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
              let uu____73703 = ctrl_tac_fold f env ctrl t  in
              bind uu____73703
                (fun uu____73724  ->
                   match uu____73724 with
                   | (t1,ctrl1) ->
                       let uu____73739 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____73739
                         (fun uu____73763  ->
                            match uu____73763 with
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
                let uu____73854 =
                  let uu____73862 =
                    add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                      opts label1
                     in
                  bind uu____73862
                    (fun uu____73873  ->
                       let uu____73874 = ctrl t1  in
                       bind uu____73874
                         (fun res  ->
                            let uu____73900 = trivial ()  in
                            bind uu____73900 (fun uu____73909  -> ret res)))
                   in
                bind uu____73854
                  (fun uu____73927  ->
                     match uu____73927 with
                     | (should_rewrite,ctrl1) ->
                         if Prims.op_Negation should_rewrite
                         then ret (t1, ctrl1)
                         else
                           (let uu____73956 =
                              FStar_TypeChecker_TcTerm.tc_term
                                (let uu___2037_73965 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___2037_73965.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___2037_73965.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___2037_73965.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___2037_73965.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___2037_73965.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___2037_73965.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___2037_73965.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___2037_73965.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___2037_73965.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___2037_73965.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___2037_73965.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___2037_73965.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___2037_73965.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___2037_73965.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___2037_73965.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___2037_73965.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___2037_73965.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___2037_73965.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___2037_73965.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___2037_73965.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___2037_73965.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___2037_73965.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___2037_73965.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___2037_73965.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___2037_73965.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___2037_73965.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___2037_73965.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___2037_73965.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___2037_73965.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___2037_73965.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___2037_73965.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___2037_73965.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___2037_73965.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___2037_73965.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___2037_73965.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___2037_73965.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___2037_73965.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___2037_73965.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___2037_73965.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___2037_73965.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___2037_73965.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___2037_73965.FStar_TypeChecker_Env.nbe)
                                 }) t1
                               in
                            match uu____73956 with
                            | (t2,lcomp,g) ->
                                let uu____73976 =
                                  (let uu____73980 =
                                     FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                       lcomp
                                      in
                                   Prims.op_Negation uu____73980) ||
                                    (let uu____73983 =
                                       FStar_TypeChecker_Env.is_trivial g  in
                                     Prims.op_Negation uu____73983)
                                   in
                                if uu____73976
                                then ret (t2, globalStop)
                                else
                                  (let typ =
                                     lcomp.FStar_Syntax_Syntax.res_typ  in
                                   let uu____73999 =
                                     new_uvar "pointwise_rec" env typ  in
                                   bind uu____73999
                                     (fun uu____74020  ->
                                        match uu____74020 with
                                        | (ut,uvar_ut) ->
                                            (log ps
                                               (fun uu____74037  ->
                                                  let uu____74038 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t2
                                                     in
                                                  let uu____74040 =
                                                    FStar_Syntax_Print.term_to_string
                                                      ut
                                                     in
                                                  FStar_Util.print2
                                                    "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                    uu____74038 uu____74040);
                                             (let uu____74043 =
                                                let uu____74046 =
                                                  let uu____74047 =
                                                    FStar_TypeChecker_TcTerm.universe_of
                                                      env typ
                                                     in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____74047 typ t2 ut
                                                   in
                                                add_irrelevant_goal
                                                  "rewrite_rec equation" env
                                                  uu____74046 opts label1
                                                 in
                                              bind uu____74043
                                                (fun uu____74055  ->
                                                   let uu____74056 =
                                                     bind rewriter
                                                       (fun uu____74070  ->
                                                          let ut1 =
                                                            FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                              env ut
                                                             in
                                                          log ps
                                                            (fun uu____74076 
                                                               ->
                                                               let uu____74077
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   t2
                                                                  in
                                                               let uu____74079
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   ut1
                                                                  in
                                                               FStar_Util.print2
                                                                 "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                                 uu____74077
                                                                 uu____74079);
                                                          ret (ut1, ctrl1))
                                                      in
                                                   focus uu____74056)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term -> (Prims.bool * FStar_BigInt.t) tac) ->
    unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____74124 =
        bind get
          (fun ps  ->
             let uu____74134 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____74134 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____74172  ->
                       let uu____74173 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____74173);
                  bind dismiss_all
                    (fun uu____74178  ->
                       let uu____74179 =
                         let uu____74186 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____74186
                           keepGoing gt1
                          in
                       bind uu____74179
                         (fun uu____74196  ->
                            match uu____74196 with
                            | (gt',uu____74204) ->
                                (log ps
                                   (fun uu____74208  ->
                                      let uu____74209 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____74209);
                                 (let uu____74212 = push_goals gs  in
                                  bind uu____74212
                                    (fun uu____74217  ->
                                       let uu____74218 =
                                         let uu____74221 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____74221]  in
                                       add_goals uu____74218)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____74124
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____74246 =
        bind get
          (fun ps  ->
             let uu____74256 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____74256 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____74294  ->
                       let uu____74295 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____74295);
                  bind dismiss_all
                    (fun uu____74300  ->
                       let uu____74301 =
                         let uu____74304 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____74304 gt1
                          in
                       bind uu____74301
                         (fun gt'  ->
                            log ps
                              (fun uu____74312  ->
                                 let uu____74313 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____74313);
                            (let uu____74316 = push_goals gs  in
                             bind uu____74316
                               (fun uu____74321  ->
                                  let uu____74322 =
                                    let uu____74325 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____74325]  in
                                  add_goals uu____74322))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____74246
  
let (trefl : unit -> unit tac) =
  fun uu____74338  ->
    let uu____74341 =
      let uu____74344 = cur_goal ()  in
      bind uu____74344
        (fun g  ->
           let uu____74362 =
             let uu____74367 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____74367  in
           match uu____74362 with
           | FStar_Pervasives_Native.Some t ->
               let uu____74375 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____74375 with
                | (hd1,args) ->
                    let uu____74414 =
                      let uu____74427 =
                        let uu____74428 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____74428.FStar_Syntax_Syntax.n  in
                      (uu____74427, args)  in
                    (match uu____74414 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____74442::(l,uu____74444)::(r,uu____74446)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____74493 =
                           let uu____74497 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____74497 l r  in
                         bind uu____74493
                           (fun b  ->
                              if b
                              then solve' g FStar_Syntax_Util.exp_unit
                              else
                                (let l1 =
                                   let uu____74508 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____74508 l
                                    in
                                 let r1 =
                                   let uu____74510 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____74510 r
                                    in
                                 let uu____74511 =
                                   let uu____74515 =
                                     FStar_Tactics_Types.goal_env g  in
                                   do_unify uu____74515 l1 r1  in
                                 bind uu____74511
                                   (fun b1  ->
                                      if b1
                                      then
                                        solve' g FStar_Syntax_Util.exp_unit
                                      else
                                        (let uu____74525 =
                                           let uu____74527 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____74527 l1  in
                                         let uu____74528 =
                                           let uu____74530 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____74530 r1  in
                                         fail2
                                           "not a trivial equality ((%s) vs (%s))"
                                           uu____74525 uu____74528))))
                     | (hd2,uu____74533) ->
                         let uu____74550 =
                           let uu____74552 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____74552 t  in
                         fail1 "trefl: not an equality (%s)" uu____74550))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____74341
  
let (dup : unit -> unit tac) =
  fun uu____74569  ->
    let uu____74572 = cur_goal ()  in
    bind uu____74572
      (fun g  ->
         let uu____74578 =
           let uu____74585 = FStar_Tactics_Types.goal_env g  in
           let uu____74586 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____74585 uu____74586  in
         bind uu____74578
           (fun uu____74596  ->
              match uu____74596 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___2129_74606 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___2129_74606.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___2129_74606.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___2129_74606.FStar_Tactics_Types.is_guard);
                      FStar_Tactics_Types.label =
                        (uu___2129_74606.FStar_Tactics_Types.label)
                    }  in
                  bind __dismiss
                    (fun uu____74609  ->
                       let uu____74610 =
                         let uu____74613 = FStar_Tactics_Types.goal_env g  in
                         let uu____74614 =
                           let uu____74615 =
                             let uu____74616 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____74617 =
                               FStar_Tactics_Types.goal_type g  in
                             FStar_TypeChecker_TcTerm.universe_of uu____74616
                               uu____74617
                              in
                           let uu____74618 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____74619 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____74615 uu____74618 u
                             uu____74619
                            in
                         add_irrelevant_goal "dup equation" uu____74613
                           uu____74614 g.FStar_Tactics_Types.opts
                           g.FStar_Tactics_Types.label
                          in
                       bind uu____74610
                         (fun uu____74623  ->
                            let uu____74624 = add_goals [g']  in
                            bind uu____74624 (fun uu____74628  -> ret ())))))
  
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
              let uu____74754 = f x y  in
              if uu____74754 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____74777 -> (acc, l11, l21)  in
        let uu____74792 = aux [] l1 l2  in
        match uu____74792 with | (pr,t1,t2) -> ((FStar_List.rev pr), t1, t2)
  
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
      let uu____74898 = get_phi g1  in
      match uu____74898 with
      | FStar_Pervasives_Native.None  -> fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____74905 = get_phi g2  in
          (match uu____74905 with
           | FStar_Pervasives_Native.None  -> fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let uu____74918 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2)
                  in
               (match uu____74918 with
                | (gamma,r1,r2) ->
                    let t1 =
                      let uu____74949 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1)
                         in
                      close_forall_no_univs1 uu____74949 phi1  in
                    let t2 =
                      let uu____74959 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2)
                         in
                      close_forall_no_univs1 uu____74959 phi2  in
                    let uu____74968 =
                      set_solution g1 FStar_Syntax_Util.exp_unit  in
                    bind uu____74968
                      (fun uu____74973  ->
                         let uu____74974 =
                           set_solution g2 FStar_Syntax_Util.exp_unit  in
                         bind uu____74974
                           (fun uu____74981  ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2  in
                              let nenv =
                                let uu___2180_74986 =
                                  FStar_Tactics_Types.goal_env g1  in
                                let uu____74987 =
                                  FStar_Util.smap_create
                                    (Prims.parse_int "100")
                                   in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___2180_74986.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___2180_74986.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___2180_74986.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___2180_74986.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____74987;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___2180_74986.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___2180_74986.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___2180_74986.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___2180_74986.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___2180_74986.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___2180_74986.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___2180_74986.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___2180_74986.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___2180_74986.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___2180_74986.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___2180_74986.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___2180_74986.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___2180_74986.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___2180_74986.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___2180_74986.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___2180_74986.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___2180_74986.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___2180_74986.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___2180_74986.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___2180_74986.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___2180_74986.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___2180_74986.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___2180_74986.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___2180_74986.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___2180_74986.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___2180_74986.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___2180_74986.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___2180_74986.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___2180_74986.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___2180_74986.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___2180_74986.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___2180_74986.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___2180_74986.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___2180_74986.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___2180_74986.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___2180_74986.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___2180_74986.FStar_TypeChecker_Env.nbe)
                                }  in
                              let uu____74991 =
                                mk_irrelevant_goal "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                  g1.FStar_Tactics_Types.label
                                 in
                              bind uu____74991
                                (fun goal  ->
                                   mlog
                                     (fun uu____75001  ->
                                        let uu____75002 =
                                          goal_to_string_verbose g1  in
                                        let uu____75004 =
                                          goal_to_string_verbose g2  in
                                        let uu____75006 =
                                          goal_to_string_verbose goal  in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____75002 uu____75004 uu____75006)
                                     (fun uu____75010  -> ret goal))))))
  
let (join : unit -> unit tac) =
  fun uu____75018  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____75034 =
               set
                 (let uu___2195_75039 = ps  in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___2195_75039.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.main_goal =
                      (uu___2195_75039.FStar_Tactics_Types.main_goal);
                    FStar_Tactics_Types.all_implicits =
                      (uu___2195_75039.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___2195_75039.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___2195_75039.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___2195_75039.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___2195_75039.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___2195_75039.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___2195_75039.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___2195_75039.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___2195_75039.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___2195_75039.FStar_Tactics_Types.local_state)
                  })
                in
             bind uu____75034
               (fun uu____75042  ->
                  let uu____75043 = join_goals g1 g2  in
                  bind uu____75043 (fun g12  -> add_goals [g12]))
         | uu____75048 -> fail "join: less than 2 goals")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) tac)
  =
  fun t  ->
    let uu____75070 =
      let uu____75077 = cur_goal ()  in
      bind uu____75077
        (fun g  ->
           let uu____75087 =
             let uu____75096 = FStar_Tactics_Types.goal_env g  in
             __tc uu____75096 t  in
           bind uu____75087
             (fun uu____75124  ->
                match uu____75124 with
                | (t1,typ,guard) ->
                    let uu____75140 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____75140 with
                     | (hd1,args) ->
                         let uu____75189 =
                           let uu____75204 =
                             let uu____75205 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____75205.FStar_Syntax_Syntax.n  in
                           (uu____75204, args)  in
                         (match uu____75189 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____75226)::(q,uu____75228)::[]) when
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
                                let uu____75282 =
                                  let uu____75283 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____75283
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____75282
                                 in
                              let g2 =
                                let uu____75285 =
                                  let uu____75286 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____75286
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____75285
                                 in
                              bind __dismiss
                                (fun uu____75293  ->
                                   let uu____75294 = add_goals [g1; g2]  in
                                   bind uu____75294
                                     (fun uu____75303  ->
                                        let uu____75304 =
                                          let uu____75309 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____75310 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____75309, uu____75310)  in
                                        ret uu____75304))
                          | uu____75315 ->
                              let uu____75330 =
                                let uu____75332 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____75332 typ  in
                              fail1 "Not a disjunction: %s" uu____75330))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____75070
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____75367 =
      let uu____75370 = cur_goal ()  in
      bind uu____75370
        (fun g  ->
           FStar_Options.push ();
           (let uu____75383 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____75383);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___2232_75390 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___2232_75390.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___2232_75390.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___2232_75390.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___2232_75390.FStar_Tactics_Types.label)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____75367
  
let (top_env : unit -> env tac) =
  fun uu____75407  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____75422  ->
    let uu____75426 = cur_goal ()  in
    bind uu____75426
      (fun g  ->
         let uu____75433 =
           (FStar_Options.lax ()) ||
             (let uu____75436 = FStar_Tactics_Types.goal_env g  in
              uu____75436.FStar_TypeChecker_Env.lax)
            in
         ret uu____75433)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____75453 =
        mlog
          (fun uu____75458  ->
             let uu____75459 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____75459)
          (fun uu____75464  ->
             let uu____75465 = cur_goal ()  in
             bind uu____75465
               (fun goal  ->
                  let env =
                    let uu____75473 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____75473 ty  in
                  let uu____75474 = __tc_ghost env tm  in
                  bind uu____75474
                    (fun uu____75493  ->
                       match uu____75493 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____75507  ->
                                let uu____75508 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____75508)
                             (fun uu____75512  ->
                                mlog
                                  (fun uu____75515  ->
                                     let uu____75516 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____75516)
                                  (fun uu____75521  ->
                                     let uu____75522 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____75522
                                       (fun uu____75527  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____75453
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____75552 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____75558 =
              let uu____75565 =
                let uu____75566 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____75566
                 in
              new_uvar "uvar_env.2" env uu____75565  in
            bind uu____75558
              (fun uu____75583  ->
                 match uu____75583 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____75552
        (fun typ  ->
           let uu____75595 = new_uvar "uvar_env" env typ  in
           bind uu____75595
             (fun uu____75610  ->
                match uu____75610 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____75629 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____75648 -> g.FStar_Tactics_Types.opts
             | uu____75651 -> FStar_Options.peek ()  in
           let uu____75654 = FStar_Syntax_Util.head_and_args t  in
           match uu____75654 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____75674);
                FStar_Syntax_Syntax.pos = uu____75675;
                FStar_Syntax_Syntax.vars = uu____75676;_},uu____75677)
               ->
               let env1 =
                 let uu___2286_75719 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___2286_75719.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___2286_75719.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___2286_75719.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___2286_75719.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___2286_75719.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___2286_75719.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___2286_75719.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___2286_75719.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___2286_75719.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___2286_75719.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___2286_75719.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___2286_75719.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___2286_75719.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___2286_75719.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___2286_75719.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___2286_75719.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___2286_75719.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___2286_75719.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___2286_75719.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___2286_75719.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___2286_75719.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___2286_75719.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___2286_75719.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___2286_75719.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___2286_75719.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___2286_75719.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___2286_75719.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___2286_75719.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___2286_75719.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___2286_75719.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___2286_75719.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___2286_75719.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___2286_75719.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___2286_75719.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___2286_75719.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___2286_75719.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___2286_75719.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___2286_75719.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___2286_75719.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___2286_75719.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___2286_75719.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___2286_75719.FStar_TypeChecker_Env.nbe)
                 }  in
               let g =
                 FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false ""  in
               let uu____75723 =
                 let uu____75726 = bnorm_goal g  in [uu____75726]  in
               add_goals uu____75723
           | uu____75727 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____75629
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____75789 = if b then t2 else ret false  in
             bind uu____75789 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____75815 = trytac comp  in
      bind uu____75815
        (fun uu___613_75827  ->
           match uu___613_75827 with
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
        let uu____75869 =
          bind get
            (fun ps  ->
               let uu____75877 = __tc e t1  in
               bind uu____75877
                 (fun uu____75898  ->
                    match uu____75898 with
                    | (t11,ty1,g1) ->
                        let uu____75911 = __tc e t2  in
                        bind uu____75911
                          (fun uu____75932  ->
                             match uu____75932 with
                             | (t21,ty2,g2) ->
                                 let uu____75945 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____75945
                                   (fun uu____75952  ->
                                      let uu____75953 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____75953
                                        (fun uu____75961  ->
                                           let uu____75962 =
                                             do_unify e ty1 ty2  in
                                           let uu____75966 =
                                             do_unify e t11 t21  in
                                           tac_and uu____75962 uu____75966)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____75869
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____76014  ->
             let uu____76015 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____76015
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
        (fun uu____76049  ->
           let uu____76050 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____76050)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____76061 =
      mlog
        (fun uu____76066  ->
           let uu____76067 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____76067)
        (fun uu____76072  ->
           let uu____76073 = cur_goal ()  in
           bind uu____76073
             (fun g  ->
                let uu____76079 =
                  let uu____76088 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____76088 ty  in
                bind uu____76079
                  (fun uu____76100  ->
                     match uu____76100 with
                     | (ty1,uu____76110,guard) ->
                         let uu____76112 =
                           let uu____76115 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____76115 guard  in
                         bind uu____76112
                           (fun uu____76119  ->
                              let uu____76120 =
                                let uu____76124 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____76125 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____76124 uu____76125 ty1  in
                              bind uu____76120
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____76134 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____76134
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops]  in
                                      let ng =
                                        let uu____76141 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____76142 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____76141
                                          uu____76142
                                         in
                                      let nty =
                                        let uu____76144 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____76144 ty1  in
                                      let uu____76145 =
                                        let uu____76149 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____76149 ng nty  in
                                      bind uu____76145
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____76158 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____76158
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____76061
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) Prims.list tac)
  =
  fun s_tm  ->
    let uu____76232 =
      let uu____76241 = cur_goal ()  in
      bind uu____76241
        (fun g  ->
           let uu____76253 =
             let uu____76262 = FStar_Tactics_Types.goal_env g  in
             __tc uu____76262 s_tm  in
           bind uu____76253
             (fun uu____76280  ->
                match uu____76280 with
                | (s_tm1,s_ty,guard) ->
                    let uu____76298 =
                      let uu____76301 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____76301 guard  in
                    bind uu____76298
                      (fun uu____76314  ->
                         let uu____76315 =
                           FStar_Syntax_Util.head_and_args' s_ty  in
                         match uu____76315 with
                         | (h,args) ->
                             let uu____76360 =
                               let uu____76367 =
                                 let uu____76368 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____76368.FStar_Syntax_Syntax.n  in
                               match uu____76367 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____76383;
                                      FStar_Syntax_Syntax.vars = uu____76384;_},us)
                                   -> ret (fv, us)
                               | uu____76394 -> fail "type is not an fv"  in
                             bind uu____76360
                               (fun uu____76415  ->
                                  match uu____76415 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____76431 =
                                        let uu____76434 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____76434 t_lid
                                         in
                                      (match uu____76431 with
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
                                                  (fun uu____76485  ->
                                                     let uu____76486 =
                                                       FStar_Syntax_Subst.open_term
                                                         t_ps t_ty
                                                        in
                                                     match uu____76486 with
                                                     | (t_ps1,t_ty1) ->
                                                         let uu____76501 =
                                                           mapM
                                                             (fun c_lid  ->
                                                                let uu____76529
                                                                  =
                                                                  let uu____76532
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                  FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____76532
                                                                    c_lid
                                                                   in
                                                                match uu____76529
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
                                                                    uu____76606
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
                                                                    let uu____76611
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____76611
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____76634
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____76634
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____76677
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs
                                                                     in
                                                                    (match uu____76677
                                                                    with
                                                                    | 
                                                                    (d_ps,bs1)
                                                                    ->
                                                                    let uu____76750
                                                                    =
                                                                    let uu____76752
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp  in
                                                                    Prims.op_Negation
                                                                    uu____76752
                                                                     in
                                                                    failwhen
                                                                    uu____76750
                                                                    "not total?"
                                                                    (fun
                                                                    uu____76771
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
                                                                    uu___614_76788
                                                                    =
                                                                    match uu___614_76788
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____76792)
                                                                    -> true
                                                                    | 
                                                                    uu____76795
                                                                    -> false
                                                                     in
                                                                    let uu____76799
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____76799
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
                                                                    uu____76933
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
                                                                    uu____76995
                                                                     ->
                                                                    match uu____76995
                                                                    with
                                                                    | 
                                                                    ((bv,uu____77015),
                                                                    (t,uu____77017))
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
                                                                    uu____77087
                                                                     ->
                                                                    match uu____77087
                                                                    with
                                                                    | 
                                                                    ((bv,uu____77114),
                                                                    (t,uu____77116))
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
                                                                    uu____77175
                                                                     ->
                                                                    match uu____77175
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
                                                                    let uu____77230
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___2450_77247
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___2450_77247.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___2450_77247.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___2450_77247.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___2450_77247.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___2450_77247.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___2450_77247.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___2450_77247.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___2450_77247.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___2450_77247.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___2450_77247.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___2450_77247.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___2450_77247.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___2450_77247.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___2450_77247.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___2450_77247.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___2450_77247.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___2450_77247.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___2450_77247.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___2450_77247.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___2450_77247.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___2450_77247.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___2450_77247.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___2450_77247.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___2450_77247.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___2450_77247.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___2450_77247.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___2450_77247.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___2450_77247.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___2450_77247.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___2450_77247.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___2450_77247.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___2450_77247.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___2450_77247.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___2450_77247.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___2450_77247.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___2450_77247.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___2450_77247.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___2450_77247.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___2450_77247.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___2450_77247.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___2450_77247.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___2450_77247.FStar_TypeChecker_Env.nbe)
                                                                    }) s_ty
                                                                    pat  in
                                                                    match uu____77230
                                                                    with
                                                                    | 
                                                                    (uu____77261,uu____77262,uu____77263,pat_t,uu____77265,_guard_pat)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____77272
                                                                    =
                                                                    let uu____77273
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____77273
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____77272
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____77278
                                                                    =
                                                                    let uu____77287
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____77287]
                                                                     in
                                                                    let uu____77306
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____77278
                                                                    uu____77306
                                                                     in
                                                                    let nty =
                                                                    let uu____77312
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____77312
                                                                     in
                                                                    let uu____77315
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____77315
                                                                    (fun
                                                                    uu____77345
                                                                     ->
                                                                    match uu____77345
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
                                                                    let uu____77372
                                                                    =
                                                                    let uu____77383
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____77383]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____77372
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____77419
                                                                    =
                                                                    let uu____77430
                                                                    =
                                                                    let uu____77435
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2)  in
                                                                    (fv1,
                                                                    uu____77435)
                                                                     in
                                                                    (g', br,
                                                                    uu____77430)
                                                                     in
                                                                    ret
                                                                    uu____77419))))))
                                                                    | 
                                                                    uu____77456
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                             c_lids
                                                            in
                                                         bind uu____76501
                                                           (fun goal_brs  ->
                                                              let uu____77506
                                                                =
                                                                FStar_List.unzip3
                                                                  goal_brs
                                                                 in
                                                              match uu____77506
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
                                                                  let uu____77579
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                  bind
                                                                    uu____77579
                                                                    (
                                                                    fun
                                                                    uu____77590
                                                                     ->
                                                                    let uu____77591
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____77591
                                                                    (fun
                                                                    uu____77601
                                                                     ->
                                                                    ret infos))))
                                            | uu____77608 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____76232
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____77657::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____77687 = init xs  in x :: uu____77687
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____77700 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      let t3 = FStar_Syntax_Util.unlazy_emb t2  in
      match t3.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____77709) -> inspect t4
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____77775 = last args  in
          (match uu____77775 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____77805 =
                 let uu____77806 =
                   let uu____77811 =
                     let uu____77812 =
                       let uu____77817 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____77817  in
                     uu____77812 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____77811, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____77806  in
               FStar_All.pipe_left ret uu____77805)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____77828,uu____77829) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
          let uu____77882 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____77882 with
           | (bs1,t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____77924 =
                      let uu____77925 =
                        let uu____77930 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____77930)  in
                      FStar_Reflection_Data.Tv_Abs uu____77925  in
                    FStar_All.pipe_left ret uu____77924))
      | FStar_Syntax_Syntax.Tm_type uu____77933 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____77958 ->
          let uu____77973 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____77973 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____78004 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____78004 with
           | (b',t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____78057 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____78070 =
            let uu____78071 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____78071  in
          FStar_All.pipe_left ret uu____78070
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____78092 =
            let uu____78093 =
              let uu____78098 =
                let uu____78099 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____78099  in
              (uu____78098, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____78093  in
          FStar_All.pipe_left ret uu____78092
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____78139 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____78144 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____78144 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____78197 ->
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
             | FStar_Util.Inr uu____78239 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____78243 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____78243 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____78263 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____78269 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____78324 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____78324
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____78345 =
                  let uu____78352 =
                    FStar_List.map
                      (fun uu____78365  ->
                         match uu____78365 with
                         | (p1,uu____78374) -> inspect_pat p1) ps
                     in
                  (fv, uu____78352)  in
                FStar_Reflection_Data.Pat_Cons uu____78345
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
              (fun uu___615_78470  ->
                 match uu___615_78470 with
                 | (pat,uu____78492,t5) ->
                     let uu____78510 = inspect_pat pat  in (uu____78510, t5))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____78519 ->
          ((let uu____78521 =
              let uu____78527 =
                let uu____78529 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____78531 = FStar_Syntax_Print.term_to_string t3  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____78529 uu____78531
                 in
              (FStar_Errors.Warning_CantInspect, uu____78527)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____78521);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____77700
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____78549 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____78549
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____78553 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____78553
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____78557 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____78557
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____78564 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____78564
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____78589 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____78589
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____78606 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____78606
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____78625 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____78625
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____78629 =
          let uu____78630 =
            let uu____78637 =
              let uu____78638 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____78638  in
            FStar_Syntax_Syntax.mk uu____78637  in
          uu____78630 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____78629
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____78643 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____78643
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____78654 =
          let uu____78655 =
            let uu____78662 =
              let uu____78663 =
                let uu____78677 =
                  let uu____78680 =
                    let uu____78681 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____78681]  in
                  FStar_Syntax_Subst.close uu____78680 t2  in
                ((false, [lb]), uu____78677)  in
              FStar_Syntax_Syntax.Tm_let uu____78663  in
            FStar_Syntax_Syntax.mk uu____78662  in
          uu____78655 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____78654
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____78723 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____78723 with
         | (lbs,body) ->
             let uu____78738 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____78738)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____78775 =
                let uu____78776 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____78776  in
              FStar_All.pipe_left wrap uu____78775
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____78783 =
                let uu____78784 =
                  let uu____78798 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____78816 = pack_pat p1  in
                         (uu____78816, false)) ps
                     in
                  (fv, uu____78798)  in
                FStar_Syntax_Syntax.Pat_cons uu____78784  in
              FStar_All.pipe_left wrap uu____78783
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
            (fun uu___616_78865  ->
               match uu___616_78865 with
               | (pat,t1) ->
                   let uu____78882 = pack_pat pat  in
                   (uu____78882, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____78930 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____78930
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____78958 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____78958
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____79004 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____79004
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____79043 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____79043
  
let (lget :
  FStar_Reflection_Data.typ -> Prims.string -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun k  ->
      let uu____79063 =
        bind get
          (fun ps  ->
             let uu____79069 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____79069 with
             | FStar_Pervasives_Native.None  -> fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
      FStar_All.pipe_left (wrap_err "lget") uu____79063
  
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit tac)
  =
  fun _ty  ->
    fun k  ->
      fun t  ->
        let uu____79103 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___2748_79110 = ps  in
                 let uu____79111 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t
                    in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___2748_79110.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___2748_79110.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___2748_79110.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___2748_79110.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___2748_79110.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___2748_79110.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___2748_79110.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___2748_79110.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___2748_79110.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___2748_79110.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___2748_79110.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___2748_79110.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____79111
                 }  in
               set ps1)
           in
        FStar_All.pipe_left (wrap_err "lset") uu____79103
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal * FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun typ  ->
      let uu____79138 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____79138 with
      | (u,ctx_uvars,g_u) ->
          let uu____79171 = FStar_List.hd ctx_uvars  in
          (match uu____79171 with
           | (ctx_uvar,uu____79185) ->
               let g =
                 let uu____79187 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____79187 false
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
        let uu____79210 = goal_of_goal_ty env typ  in
        match uu____79210 with
        | (g,g_u) ->
            let ps =
              let uu____79222 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "TacVerbose")
                 in
              let uu____79225 = FStar_Util.psmap_empty ()  in
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
                FStar_Tactics_Types.tac_verb_dbg = uu____79222;
                FStar_Tactics_Types.local_state = uu____79225
              }  in
            let uu____79235 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____79235)
  