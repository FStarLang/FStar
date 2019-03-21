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
    let uu____63906 =
      let uu____63907 = FStar_Tactics_Types.goal_env g  in
      let uu____63908 = FStar_Tactics_Types.goal_type g  in
      bnorm uu____63907 uu____63908  in
    FStar_Tactics_Types.goal_with_type g uu____63906
  
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
      let uu____64022 = FStar_Options.tactics_failhard ()  in
      if uu____64022
      then run t p
      else
        (try (fun uu___640_64032  -> match () with | () -> run t p) ()
         with
         | FStar_Errors.Err (uu____64041,msg) ->
             FStar_Tactics_Result.Failed
               ((FStar_Tactics_Types.TacticFailure msg), p)
         | FStar_Errors.Error (uu____64045,msg,uu____64047) ->
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
           let uu____64127 = run t1 p  in
           match uu____64127 with
           | FStar_Tactics_Result.Success (a,q) ->
               let uu____64134 = t2 a  in run uu____64134 q
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
    let uu____64157 =
      FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head  in
    match uu____64157 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (check_goal_solved :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun goal  -> get_uvar_solved goal.FStar_Tactics_Types.goal_ctx_uvar 
let (goal_to_string_verbose : FStar_Tactics_Types.goal -> Prims.string) =
  fun g  ->
    let uu____64179 =
      FStar_Syntax_Print.ctx_uvar_to_string
        g.FStar_Tactics_Types.goal_ctx_uvar
       in
    let uu____64181 =
      let uu____64183 = check_goal_solved g  in
      match uu____64183 with
      | FStar_Pervasives_Native.None  -> ""
      | FStar_Pervasives_Native.Some t ->
          let uu____64189 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "\tGOAL ALREADY SOLVED!: %s" uu____64189
       in
    FStar_Util.format2 "%s%s\n" uu____64179 uu____64181
  
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
            let uu____64236 = FStar_Options.print_implicits ()  in
            if uu____64236
            then
              let uu____64240 = FStar_Tactics_Types.goal_env g  in
              let uu____64241 = FStar_Tactics_Types.goal_witness g  in
              tts uu____64240 uu____64241
            else
              (let uu____64244 =
                 get_uvar_solved g.FStar_Tactics_Types.goal_ctx_uvar  in
               match uu____64244 with
               | FStar_Pervasives_Native.None  -> "_"
               | FStar_Pervasives_Native.Some t ->
                   let uu____64250 = FStar_Tactics_Types.goal_env g  in
                   let uu____64251 = FStar_Tactics_Types.goal_witness g  in
                   tts uu____64250 uu____64251)
             in
          let num =
            match maybe_num with
            | FStar_Pervasives_Native.None  -> ""
            | FStar_Pervasives_Native.Some (i,n1) ->
                let uu____64274 = FStar_Util.string_of_int i  in
                let uu____64276 = FStar_Util.string_of_int n1  in
                FStar_Util.format2 " %s/%s" uu____64274 uu____64276
             in
          let maybe_label =
            match g.FStar_Tactics_Types.label with
            | "" -> ""
            | l -> Prims.op_Hat " (" (Prims.op_Hat l ")")  in
          let actual_goal =
            if ps.FStar_Tactics_Types.tac_verb_dbg
            then goal_to_string_verbose g
            else
              (let uu____64294 =
                 FStar_Syntax_Print.binders_to_string ", "
                   (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
                  in
               let uu____64297 =
                 let uu____64299 = FStar_Tactics_Types.goal_env g  in
                 tts uu____64299
                   (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                  in
               FStar_Util.format3 "%s |- %s : %s\n" uu____64294 w uu____64297)
             in
          FStar_Util.format4 "%s%s%s:\n%s\n" kind num maybe_label actual_goal
  
let (tacprint : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      let uu____64326 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____64326
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____64351 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____64351
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____64383 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____64383
  
let (comp_to_typ : FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____64393) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____64403) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (get_phi :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun g  ->
    let uu____64423 =
      let uu____64424 = FStar_Tactics_Types.goal_env g  in
      let uu____64425 = FStar_Tactics_Types.goal_type g  in
      FStar_TypeChecker_Normalize.unfold_whnf uu____64424 uu____64425  in
    FStar_Syntax_Util.un_squash uu____64423
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  -> let uu____64434 = get_phi g  in FStar_Option.isSome uu____64434 
let (print : Prims.string -> unit tac) = fun msg  -> tacprint msg; ret () 
let (debugging : unit -> Prims.bool tac) =
  fun uu____64458  ->
    bind get
      (fun ps  ->
         let uu____64466 =
           FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
             (FStar_Options.Other "Tac")
            in
         ret uu____64466)
  
let (ps_to_string :
  (Prims.string * FStar_Tactics_Types.proofstate) -> Prims.string) =
  fun uu____64481  ->
    match uu____64481 with
    | (msg,ps) ->
        let p_imp imp =
          FStar_Syntax_Print.uvar_to_string
            (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
           in
        let n_active = FStar_List.length ps.FStar_Tactics_Types.goals  in
        let n_smt = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
        let n1 = n_active + n_smt  in
        let uu____64503 =
          let uu____64507 =
            let uu____64511 =
              let uu____64513 =
                FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
              FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____64513
                msg
               in
            let uu____64516 =
              let uu____64520 =
                if
                  ps.FStar_Tactics_Types.entry_range <>
                    FStar_Range.dummyRange
                then
                  let uu____64524 =
                    FStar_Range.string_of_def_range
                      ps.FStar_Tactics_Types.entry_range
                     in
                  FStar_Util.format1 "Location: %s\n" uu____64524
                else ""  in
              let uu____64530 =
                let uu____64534 =
                  let uu____64536 =
                    FStar_TypeChecker_Env.debug
                      ps.FStar_Tactics_Types.main_context
                      (FStar_Options.Other "Imp")
                     in
                  if uu____64536
                  then
                    let uu____64541 =
                      FStar_Common.string_of_list p_imp
                        ps.FStar_Tactics_Types.all_implicits
                       in
                    FStar_Util.format1 "Imps: %s\n" uu____64541
                  else ""  in
                [uu____64534]  in
              uu____64520 :: uu____64530  in
            uu____64511 :: uu____64516  in
          let uu____64551 =
            let uu____64555 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "Goal"
                       (FStar_Pervasives_Native.Some
                          (((Prims.parse_int "1") + i), n1)) ps g)
                ps.FStar_Tactics_Types.goals
               in
            let uu____64575 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "SMT Goal"
                       (FStar_Pervasives_Native.Some
                          ((((Prims.parse_int "1") + n_active) + i), n1)) ps
                       g) ps.FStar_Tactics_Types.smt_goals
               in
            FStar_List.append uu____64555 uu____64575  in
          FStar_List.append uu____64507 uu____64551  in
        FStar_String.concat "" uu____64503
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      let uu____64605 =
        let uu____64606 = FStar_Tactics_Types.goal_env g  in
        FStar_TypeChecker_Env.all_binders uu____64606  in
      let uu____64607 =
        let uu____64612 =
          let uu____64613 = FStar_Tactics_Types.goal_env g  in
          FStar_TypeChecker_Env.dsenv uu____64613  in
        FStar_Syntax_Print.binders_to_json uu____64612  in
      FStar_All.pipe_right uu____64605 uu____64607  in
    let uu____64614 =
      let uu____64622 =
        let uu____64630 =
          let uu____64636 =
            let uu____64637 =
              let uu____64645 =
                let uu____64651 =
                  let uu____64652 =
                    let uu____64654 = FStar_Tactics_Types.goal_env g  in
                    let uu____64655 = FStar_Tactics_Types.goal_witness g  in
                    tts uu____64654 uu____64655  in
                  FStar_Util.JsonStr uu____64652  in
                ("witness", uu____64651)  in
              let uu____64658 =
                let uu____64666 =
                  let uu____64672 =
                    let uu____64673 =
                      let uu____64675 = FStar_Tactics_Types.goal_env g  in
                      let uu____64676 = FStar_Tactics_Types.goal_type g  in
                      tts uu____64675 uu____64676  in
                    FStar_Util.JsonStr uu____64673  in
                  ("type", uu____64672)  in
                [uu____64666;
                ("label", (FStar_Util.JsonStr (g.FStar_Tactics_Types.label)))]
                 in
              uu____64645 :: uu____64658  in
            FStar_Util.JsonAssoc uu____64637  in
          ("goal", uu____64636)  in
        [uu____64630]  in
      ("hyps", g_binders) :: uu____64622  in
    FStar_Util.JsonAssoc uu____64614
  
let (ps_to_json :
  (Prims.string * FStar_Tactics_Types.proofstate) -> FStar_Util.json) =
  fun uu____64730  ->
    match uu____64730 with
    | (msg,ps) ->
        let uu____64740 =
          let uu____64748 =
            let uu____64756 =
              let uu____64764 =
                let uu____64772 =
                  let uu____64778 =
                    let uu____64779 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____64779  in
                  ("goals", uu____64778)  in
                let uu____64784 =
                  let uu____64792 =
                    let uu____64798 =
                      let uu____64799 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____64799  in
                    ("smt-goals", uu____64798)  in
                  [uu____64792]  in
                uu____64772 :: uu____64784  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____64764
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____64756  in
          let uu____64833 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____64849 =
                let uu____64855 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____64855)  in
              [uu____64849]
            else []  in
          FStar_List.append uu____64748 uu____64833  in
        FStar_Util.JsonAssoc uu____64740
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____64895  ->
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
         (let uu____64926 = FStar_Tactics_Types.subst_proof_state subst1 ps
             in
          dump_proofstate uu____64926 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let traise : 'a . Prims.exn -> 'a tac =
  fun e  -> mk_tac (fun ps  -> FStar_Tactics_Result.Failed (e, ps)) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____64999 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____64999
          then dump_proofstate ps (Prims.op_Hat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed
           ((FStar_Tactics_Types.TacticFailure msg), ps))
  
let fail1 : 'Auu____65013 . Prims.string -> Prims.string -> 'Auu____65013 tac
  =
  fun msg  ->
    fun x  -> let uu____65030 = FStar_Util.format1 msg x  in fail uu____65030
  
let fail2 :
  'Auu____65041 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____65041 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        let uu____65065 = FStar_Util.format2 msg x y  in fail uu____65065
  
let fail3 :
  'Auu____65078 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____65078 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____65109 = FStar_Util.format3 msg x y z  in fail uu____65109
  
let fail4 :
  'Auu____65124 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____65124 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____65162 = FStar_Util.format4 msg x y z w  in
            fail uu____65162
  
let catch : 'a . 'a tac -> (Prims.exn,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____65197 = run t ps  in
         match uu____65197 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___802_65221 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___802_65221.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___802_65221.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___802_65221.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___802_65221.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___802_65221.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___802_65221.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___802_65221.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___802_65221.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___802_65221.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___802_65221.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___802_65221.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (uu___802_65221.FStar_Tactics_Types.local_state)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let recover : 'a . 'a tac -> (Prims.exn,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let uu____65260 = run t ps  in
         match uu____65260 with
         | FStar_Tactics_Result.Success (a,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inr a), q)
         | FStar_Tactics_Result.Failed (m,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inl m), q))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____65308 = catch t  in
    bind uu____65308
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____65335 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try
           (fun uu___828_65367  ->
              match () with
              | () -> let uu____65372 = trytac t  in run uu____65372 ps) ()
         with
         | FStar_Errors.Err (uu____65388,msg) ->
             (log ps
                (fun uu____65394  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____65400,msg,uu____65402) ->
             (log ps
                (fun uu____65407  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____65444 = run t ps  in
           match uu____65444 with
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
  fun p  -> mk_tac (fun uu____65468  -> FStar_Tactics_Result.Success ((), p)) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___863_65483 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___863_65483.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___863_65483.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___863_65483.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___863_65483.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___863_65483.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___863_65483.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___863_65483.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___863_65483.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___863_65483.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___863_65483.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___863_65483.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___863_65483.FStar_Tactics_Types.local_state)
            }))
  
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____65507 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____65507
         then
           let uu____65511 = FStar_Syntax_Print.term_to_string t1  in
           let uu____65513 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____65511
             uu____65513
         else ());
        (try
           (fun uu___871_65524  ->
              match () with
              | () ->
                  let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
                  ((let uu____65532 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____65532
                    then
                      let uu____65536 =
                        FStar_Common.string_of_option
                          (FStar_TypeChecker_Rel.guard_to_string env) res
                         in
                      let uu____65538 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____65540 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.print3
                        "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____65536
                        uu____65538 uu____65540
                    else ());
                   (match res with
                    | FStar_Pervasives_Native.None  -> ret false
                    | FStar_Pervasives_Native.Some g ->
                        let uu____65551 =
                          add_implicits g.FStar_TypeChecker_Env.implicits  in
                        bind uu____65551 (fun uu____65556  -> ret true)))) ()
         with
         | FStar_Errors.Err (uu____65566,msg) ->
             mlog
               (fun uu____65572  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____65575  -> ret false)
         | FStar_Errors.Error (uu____65578,msg,r) ->
             mlog
               (fun uu____65586  ->
                  let uu____65587 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____65587) (fun uu____65591  -> ret false))
  
let (compress_implicits : unit tac) =
  bind get
    (fun ps  ->
       let imps = ps.FStar_Tactics_Types.all_implicits  in
       let g =
         let uu___897_65605 = FStar_TypeChecker_Env.trivial_guard  in
         {
           FStar_TypeChecker_Env.guard_f =
             (uu___897_65605.FStar_TypeChecker_Env.guard_f);
           FStar_TypeChecker_Env.deferred =
             (uu___897_65605.FStar_TypeChecker_Env.deferred);
           FStar_TypeChecker_Env.univ_ineqs =
             (uu___897_65605.FStar_TypeChecker_Env.univ_ineqs);
           FStar_TypeChecker_Env.implicits = imps
         }  in
       let g1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g
          in
       let ps' =
         let uu___901_65608 = ps  in
         {
           FStar_Tactics_Types.main_context =
             (uu___901_65608.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___901_65608.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (g1.FStar_TypeChecker_Env.implicits);
           FStar_Tactics_Types.goals =
             (uu___901_65608.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___901_65608.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___901_65608.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___901_65608.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___901_65608.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___901_65608.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___901_65608.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___901_65608.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___901_65608.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___901_65608.FStar_Tactics_Types.local_state)
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
          (fun uu____65635  ->
             (let uu____65637 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____65637
              then
                (FStar_Options.push ();
                 (let uu____65642 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____65646 = __do_unify env t1 t2  in
              bind uu____65646
                (fun r  ->
                   (let uu____65657 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____65657 then FStar_Options.pop () else ());
                   ret r)))
  
let (remove_solved_goals : unit tac) =
  bind get
    (fun ps  ->
       let ps' =
         let uu___916_65671 = ps  in
         let uu____65672 =
           FStar_List.filter
             (fun g  ->
                let uu____65678 = check_goal_solved g  in
                FStar_Option.isNone uu____65678) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___916_65671.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___916_65671.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___916_65671.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____65672;
           FStar_Tactics_Types.smt_goals =
             (uu___916_65671.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___916_65671.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___916_65671.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___916_65671.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___916_65671.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___916_65671.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___916_65671.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___916_65671.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___916_65671.FStar_Tactics_Types.local_state)
         }  in
       set ps')
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____65696 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____65696 with
      | FStar_Pervasives_Native.Some uu____65701 ->
          let uu____65702 =
            let uu____65704 = goal_to_string_verbose goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____65704  in
          fail uu____65702
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____65725 = FStar_Tactics_Types.goal_env goal  in
      let uu____65726 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____65725 solution uu____65726
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____65733 =
         let uu___929_65734 = p  in
         let uu____65735 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___929_65734.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___929_65734.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___929_65734.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____65735;
           FStar_Tactics_Types.smt_goals =
             (uu___929_65734.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___929_65734.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___929_65734.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___929_65734.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___929_65734.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___929_65734.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___929_65734.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___929_65734.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___929_65734.FStar_Tactics_Types.local_state)
         }  in
       set uu____65733)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      mlog
        (fun uu____65757  ->
           let uu____65758 =
             let uu____65760 = FStar_Tactics_Types.goal_witness goal  in
             FStar_Syntax_Print.term_to_string uu____65760  in
           let uu____65761 = FStar_Syntax_Print.term_to_string solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____65758 uu____65761)
        (fun uu____65766  ->
           let uu____65767 = trysolve goal solution  in
           bind uu____65767
             (fun b  ->
                if b
                then bind __dismiss (fun uu____65779  -> remove_solved_goals)
                else
                  (let uu____65782 =
                     let uu____65784 =
                       let uu____65786 = FStar_Tactics_Types.goal_env goal
                          in
                       tts uu____65786 solution  in
                     let uu____65787 =
                       let uu____65789 = FStar_Tactics_Types.goal_env goal
                          in
                       let uu____65790 =
                         FStar_Tactics_Types.goal_witness goal  in
                       tts uu____65789 uu____65790  in
                     let uu____65791 =
                       let uu____65793 = FStar_Tactics_Types.goal_env goal
                          in
                       let uu____65794 = FStar_Tactics_Types.goal_type goal
                          in
                       tts uu____65793 uu____65794  in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____65784 uu____65787 uu____65791
                      in
                   fail uu____65782)))
  
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____65811 = set_solution goal solution  in
      bind uu____65811
        (fun uu____65815  ->
           bind __dismiss (fun uu____65817  -> remove_solved_goals))
  
let (set_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___945_65836 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___945_65836.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___945_65836.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___945_65836.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals = gs;
              FStar_Tactics_Types.smt_goals =
                (uu___945_65836.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___945_65836.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___945_65836.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___945_65836.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___945_65836.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___945_65836.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___945_65836.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___945_65836.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___945_65836.FStar_Tactics_Types.local_state)
            }))
  
let (set_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___949_65855 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___949_65855.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___949_65855.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___949_65855.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___949_65855.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals = gs;
              FStar_Tactics_Types.depth =
                (uu___949_65855.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___949_65855.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___949_65855.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___949_65855.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___949_65855.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___949_65855.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___949_65855.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___949_65855.FStar_Tactics_Types.local_state)
            }))
  
let (dismiss_all : unit tac) = set_goals [] 
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____65871 = FStar_Options.defensive ()  in
    if uu____65871
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____65881 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____65881)
         in
      let b2 =
        b1 &&
          (let uu____65885 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____65885)
         in
      let rec aux b3 e =
        let uu____65900 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____65900 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____65920 =
        (let uu____65924 = aux b2 env  in Prims.op_Negation uu____65924) &&
          (let uu____65927 = FStar_ST.op_Bang nwarn  in
           uu____65927 < (Prims.parse_int "5"))
         in
      (if uu____65920
       then
         ((let uu____65953 =
             let uu____65954 = FStar_Tactics_Types.goal_type g  in
             uu____65954.FStar_Syntax_Syntax.pos  in
           let uu____65957 =
             let uu____65963 =
               let uu____65965 = goal_to_string_verbose g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____65965
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____65963)  in
           FStar_Errors.log_issue uu____65953 uu____65957);
          (let uu____65969 =
             let uu____65971 = FStar_ST.op_Bang nwarn  in
             uu____65971 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____65969))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___971_66040 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___971_66040.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___971_66040.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___971_66040.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___971_66040.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___971_66040.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___971_66040.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___971_66040.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___971_66040.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___971_66040.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___971_66040.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___971_66040.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___971_66040.FStar_Tactics_Types.local_state)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___976_66061 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___976_66061.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___976_66061.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___976_66061.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___976_66061.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___976_66061.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___976_66061.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___976_66061.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___976_66061.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___976_66061.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___976_66061.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___976_66061.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___976_66061.FStar_Tactics_Types.local_state)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___981_66082 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___981_66082.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___981_66082.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___981_66082.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___981_66082.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___981_66082.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___981_66082.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___981_66082.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___981_66082.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___981_66082.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___981_66082.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___981_66082.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___981_66082.FStar_Tactics_Types.local_state)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___986_66103 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___986_66103.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___986_66103.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___986_66103.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___986_66103.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___986_66103.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___986_66103.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___986_66103.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___986_66103.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___986_66103.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___986_66103.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___986_66103.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___986_66103.FStar_Tactics_Types.local_state)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____66115  -> add_goals [g]) 
let (new_uvar :
  Prims.string ->
    env ->
      FStar_Reflection_Data.typ ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar) tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____66146 =
          FStar_TypeChecker_Env.new_implicit_var_aux reason
            typ.FStar_Syntax_Syntax.pos env typ
            FStar_Syntax_Syntax.Allow_untyped FStar_Pervasives_Native.None
           in
        match uu____66146 with
        | (u,ctx_uvar,g_u) ->
            let uu____66184 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____66184
              (fun uu____66193  ->
                 let uu____66194 =
                   let uu____66199 =
                     let uu____66200 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____66200  in
                   (u, uu____66199)  in
                 ret uu____66194)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____66221 = FStar_Syntax_Util.un_squash t1  in
    match uu____66221 with
    | FStar_Pervasives_Native.Some t' ->
        let t'1 = FStar_Syntax_Util.unascribe t'  in
        let uu____66233 =
          let uu____66234 = FStar_Syntax_Subst.compress t'1  in
          uu____66234.FStar_Syntax_Syntax.n  in
        (match uu____66233 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____66239 -> false)
    | uu____66241 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____66254 = FStar_Syntax_Util.un_squash t  in
    match uu____66254 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____66265 =
          let uu____66266 = FStar_Syntax_Subst.compress t'  in
          uu____66266.FStar_Syntax_Syntax.n  in
        (match uu____66265 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____66271 -> false)
    | uu____66273 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____66286  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____66298 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____66298 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____66305 = goal_to_string_verbose hd1  in
                    let uu____66307 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____66305 uu____66307);
                   ret hd1)))
  
let (tadmit_t : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____66320 =
      bind get
        (fun ps  ->
           let uu____66326 = cur_goal ()  in
           bind uu____66326
             (fun g  ->
                (let uu____66333 =
                   let uu____66334 = FStar_Tactics_Types.goal_type g  in
                   uu____66334.FStar_Syntax_Syntax.pos  in
                 let uu____66337 =
                   let uu____66343 =
                     let uu____66345 =
                       goal_to_string "" FStar_Pervasives_Native.None ps g
                        in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____66345
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____66343)  in
                 FStar_Errors.log_issue uu____66333 uu____66337);
                solve' g t))
       in
    FStar_All.pipe_left (wrap_err "tadmit_t") uu____66320
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____66368  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___1031_66379 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___1031_66379.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___1031_66379.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___1031_66379.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___1031_66379.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___1031_66379.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___1031_66379.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___1031_66379.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___1031_66379.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___1031_66379.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___1031_66379.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___1031_66379.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (uu___1031_66379.FStar_Tactics_Types.local_state)
           }  in
         let uu____66381 = set ps1  in
         bind uu____66381
           (fun uu____66386  ->
              let uu____66387 = FStar_BigInt.of_int_fs n1  in ret uu____66387))
  
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
              let uu____66425 = env.FStar_TypeChecker_Env.universe_of env phi
                 in
              FStar_Syntax_Util.mk_squash uu____66425 phi  in
            let uu____66426 = new_uvar reason env typ  in
            bind uu____66426
              (fun uu____66441  ->
                 match uu____66441 with
                 | (uu____66448,ctx_uvar) ->
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
             (fun uu____66495  ->
                let uu____66496 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____66496)
             (fun uu____66501  ->
                let e1 =
                  let uu___1049_66503 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1049_66503.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1049_66503.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1049_66503.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1049_66503.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1049_66503.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1049_66503.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1049_66503.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1049_66503.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1049_66503.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1049_66503.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1049_66503.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1049_66503.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1049_66503.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1049_66503.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1049_66503.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1049_66503.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1049_66503.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1049_66503.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1049_66503.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1049_66503.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1049_66503.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1049_66503.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1049_66503.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1049_66503.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1049_66503.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1049_66503.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1049_66503.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1049_66503.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1049_66503.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1049_66503.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1049_66503.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1049_66503.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1049_66503.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1049_66503.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1049_66503.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1049_66503.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1049_66503.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1049_66503.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1049_66503.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1049_66503.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1049_66503.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1049_66503.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___1053_66515  ->
                     match () with
                     | () ->
                         let uu____66524 =
                           FStar_TypeChecker_TcTerm.type_of_tot_term e1 t  in
                         ret uu____66524) ()
                with
                | FStar_Errors.Err (uu____66551,msg) ->
                    let uu____66555 = tts e1 t  in
                    let uu____66557 =
                      let uu____66559 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____66559
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____66555 uu____66557 msg
                | FStar_Errors.Error (uu____66569,msg,uu____66571) ->
                    let uu____66574 = tts e1 t  in
                    let uu____66576 =
                      let uu____66578 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____66578
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____66574 uu____66576 msg))
  
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
             (fun uu____66631  ->
                let uu____66632 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc_ghost(%s)\n" uu____66632)
             (fun uu____66637  ->
                let e1 =
                  let uu___1070_66639 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1070_66639.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1070_66639.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1070_66639.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1070_66639.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1070_66639.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1070_66639.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1070_66639.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1070_66639.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1070_66639.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1070_66639.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1070_66639.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1070_66639.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1070_66639.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1070_66639.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1070_66639.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1070_66639.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1070_66639.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1070_66639.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1070_66639.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1070_66639.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1070_66639.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1070_66639.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1070_66639.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1070_66639.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1070_66639.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1070_66639.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1070_66639.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1070_66639.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1070_66639.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1070_66639.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1070_66639.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1070_66639.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1070_66639.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1070_66639.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1070_66639.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1070_66639.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1070_66639.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1070_66639.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1070_66639.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1070_66639.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1070_66639.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1070_66639.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___1074_66654  ->
                     match () with
                     | () ->
                         let uu____66663 =
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e1 t
                            in
                         (match uu____66663 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____66701,msg) ->
                    let uu____66705 = tts e1 t  in
                    let uu____66707 =
                      let uu____66709 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____66709
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____66705 uu____66707 msg
                | FStar_Errors.Error (uu____66719,msg,uu____66721) ->
                    let uu____66724 = tts e1 t  in
                    let uu____66726 =
                      let uu____66728 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____66728
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____66724 uu____66726 msg))
  
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
             (fun uu____66781  ->
                let uu____66782 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____66782)
             (fun uu____66788  ->
                let e1 =
                  let uu___1095_66790 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1095_66790.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1095_66790.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1095_66790.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1095_66790.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1095_66790.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1095_66790.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1095_66790.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1095_66790.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1095_66790.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1095_66790.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1095_66790.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1095_66790.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1095_66790.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1095_66790.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1095_66790.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1095_66790.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1095_66790.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1095_66790.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1095_66790.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1095_66790.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1095_66790.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1095_66790.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1095_66790.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1095_66790.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1095_66790.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1095_66790.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1095_66790.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1095_66790.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1095_66790.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1095_66790.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1095_66790.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1095_66790.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1095_66790.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1095_66790.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1095_66790.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1095_66790.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1095_66790.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1095_66790.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1095_66790.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1095_66790.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1095_66790.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1095_66790.FStar_TypeChecker_Env.nbe)
                  }  in
                let e2 =
                  let uu___1098_66793 = e1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1098_66793.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1098_66793.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1098_66793.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1098_66793.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1098_66793.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1098_66793.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1098_66793.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1098_66793.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1098_66793.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1098_66793.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1098_66793.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1098_66793.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1098_66793.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1098_66793.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1098_66793.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1098_66793.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1098_66793.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1098_66793.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1098_66793.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1098_66793.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1098_66793.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1098_66793.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1098_66793.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1098_66793.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___1098_66793.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1098_66793.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1098_66793.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1098_66793.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1098_66793.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1098_66793.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1098_66793.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1098_66793.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1098_66793.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1098_66793.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1098_66793.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1098_66793.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1098_66793.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1098_66793.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1098_66793.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1098_66793.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1098_66793.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1098_66793.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___1102_66808  ->
                     match () with
                     | () ->
                         let uu____66817 =
                           FStar_TypeChecker_TcTerm.tc_term e2 t  in
                         (match uu____66817 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____66855,msg) ->
                    let uu____66859 = tts e2 t  in
                    let uu____66861 =
                      let uu____66863 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____66863
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____66859 uu____66861 msg
                | FStar_Errors.Error (uu____66873,msg,uu____66875) ->
                    let uu____66878 = tts e2 t  in
                    let uu____66880 =
                      let uu____66882 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____66882
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____66878 uu____66880 msg))
  
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
  fun uu____66916  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___1127_66935 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___1127_66935.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___1127_66935.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___1127_66935.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___1127_66935.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___1127_66935.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___1127_66935.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___1127_66935.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___1127_66935.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___1127_66935.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___1127_66935.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___1127_66935.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___1127_66935.FStar_Tactics_Types.local_state)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____66960 = get_guard_policy ()  in
      bind uu____66960
        (fun old_pol  ->
           let uu____66966 = set_guard_policy pol  in
           bind uu____66966
             (fun uu____66970  ->
                bind t
                  (fun r  ->
                     let uu____66974 = set_guard_policy old_pol  in
                     bind uu____66974 (fun uu____66978  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____66982 = let uu____66987 = cur_goal ()  in trytac uu____66987  in
  bind uu____66982
    (fun uu___609_66994  ->
       match uu___609_66994 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____67000 = FStar_Options.peek ()  in ret uu____67000)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        mlog
          (fun uu____67025  ->
             let uu____67026 = FStar_TypeChecker_Rel.guard_to_string e g  in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason
               uu____67026)
          (fun uu____67031  ->
             let uu____67032 =
               add_implicits g.FStar_TypeChecker_Env.implicits  in
             bind uu____67032
               (fun uu____67036  ->
                  bind getopts
                    (fun opts  ->
                       let uu____67040 =
                         let uu____67041 =
                           FStar_TypeChecker_Rel.simplify_guard e g  in
                         uu____67041.FStar_TypeChecker_Env.guard_f  in
                       match uu____67040 with
                       | FStar_TypeChecker_Common.Trivial  -> ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____67045 = istrivial e f  in
                           if uu____67045
                           then ret ()
                           else
                             bind get
                               (fun ps  ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop  ->
                                      ((let uu____67058 =
                                          let uu____67064 =
                                            let uu____67066 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g
                                               in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____67066
                                             in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____67064)
                                           in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____67058);
                                       ret ())
                                  | FStar_Tactics_Types.Goal  ->
                                      mlog
                                        (fun uu____67072  ->
                                           let uu____67073 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____67073)
                                        (fun uu____67078  ->
                                           let uu____67079 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____67079
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___1156_67087 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___1156_67087.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___1156_67087.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___1156_67087.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___1156_67087.FStar_Tactics_Types.label)
                                                  }  in
                                                push_goals [goal1]))
                                  | FStar_Tactics_Types.SMT  ->
                                      mlog
                                        (fun uu____67091  ->
                                           let uu____67092 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____67092)
                                        (fun uu____67097  ->
                                           let uu____67098 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____67098
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___1163_67106 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___1163_67106.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___1163_67106.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___1163_67106.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___1163_67106.FStar_Tactics_Types.label)
                                                  }  in
                                                push_smt_goals [goal1]))
                                  | FStar_Tactics_Types.Force  ->
                                      mlog
                                        (fun uu____67110  ->
                                           let uu____67111 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____67111)
                                        (fun uu____67115  ->
                                           try
                                             (fun uu___1170_67120  ->
                                                match () with
                                                | () ->
                                                    let uu____67123 =
                                                      let uu____67125 =
                                                        let uu____67127 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____67127
                                                         in
                                                      Prims.op_Negation
                                                        uu____67125
                                                       in
                                                    if uu____67123
                                                    then
                                                      mlog
                                                        (fun uu____67134  ->
                                                           let uu____67135 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g
                                                              in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____67135)
                                                        (fun uu____67139  ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else ret ()) ()
                                           with
                                           | uu___1169_67144 ->
                                               mlog
                                                 (fun uu____67149  ->
                                                    let uu____67150 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g
                                                       in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____67150)
                                                 (fun uu____67154  ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____67166 =
      let uu____67169 = cur_goal ()  in
      bind uu____67169
        (fun goal  ->
           let uu____67175 =
             let uu____67184 = FStar_Tactics_Types.goal_env goal  in
             __tc_lax uu____67184 t  in
           bind uu____67175
             (fun uu____67195  ->
                match uu____67195 with
                | (uu____67204,typ,uu____67206) -> ret typ))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____67166
  
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
            let uu____67246 = mk_irrelevant_goal reason env phi opts label1
               in
            bind uu____67246 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____67258  ->
    let uu____67261 = cur_goal ()  in
    bind uu____67261
      (fun goal  ->
         let uu____67267 =
           let uu____67269 = FStar_Tactics_Types.goal_env goal  in
           let uu____67270 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____67269 uu____67270  in
         if uu____67267
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____67276 =
              let uu____67278 = FStar_Tactics_Types.goal_env goal  in
              let uu____67279 = FStar_Tactics_Types.goal_type goal  in
              tts uu____67278 uu____67279  in
            fail1 "Not a trivial goal: %s" uu____67276))
  
let divide : 'a 'b . FStar_BigInt.t -> 'a tac -> 'b tac -> ('a * 'b) tac =
  fun n1  ->
    fun l  ->
      fun r  ->
        bind get
          (fun p  ->
             let uu____67330 =
               try
                 (fun uu___1226_67353  ->
                    match () with
                    | () ->
                        let uu____67364 =
                          let uu____67373 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____67373
                            p.FStar_Tactics_Types.goals
                           in
                        ret uu____67364) ()
               with | uu___1225_67384 -> fail "divide: not enough goals"  in
             bind uu____67330
               (fun uu____67421  ->
                  match uu____67421 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___1208_67447 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___1208_67447.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___1208_67447.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___1208_67447.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___1208_67447.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___1208_67447.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___1208_67447.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___1208_67447.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___1208_67447.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___1208_67447.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___1208_67447.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___1208_67447.FStar_Tactics_Types.local_state)
                        }  in
                      let uu____67448 = set lp  in
                      bind uu____67448
                        (fun uu____67456  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___1214_67472 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___1214_67472.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___1214_67472.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___1214_67472.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___1214_67472.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___1214_67472.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___1214_67472.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___1214_67472.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___1214_67472.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___1214_67472.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___1214_67472.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___1214_67472.FStar_Tactics_Types.local_state)
                                       }  in
                                     let uu____67473 = set rp  in
                                     bind uu____67473
                                       (fun uu____67481  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___1220_67497 =
                                                        rp'  in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___1220_67497.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___1220_67497.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___1220_67497.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___1220_67497.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___1220_67497.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___1220_67497.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___1220_67497.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___1220_67497.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___1220_67497.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___1220_67497.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___1220_67497.FStar_Tactics_Types.local_state)
                                                      }  in
                                                    let uu____67498 = set p'
                                                       in
                                                    bind uu____67498
                                                      (fun uu____67506  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____67512 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____67534 = divide FStar_BigInt.one f idtac  in
    bind uu____67534
      (fun uu____67547  -> match uu____67547 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____67585::uu____67586 ->
             let uu____67589 =
               let uu____67598 = map tau  in
               divide FStar_BigInt.one tau uu____67598  in
             bind uu____67589
               (fun uu____67616  ->
                  match uu____67616 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____67658 =
        bind t1
          (fun uu____67663  ->
             let uu____67664 = map t2  in
             bind uu____67664 (fun uu____67672  -> ret ()))
         in
      focus uu____67658
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____67682  ->
    let uu____67685 =
      let uu____67688 = cur_goal ()  in
      bind uu____67688
        (fun goal  ->
           let uu____67697 =
             let uu____67704 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____67704  in
           match uu____67697 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____67713 =
                 let uu____67715 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____67715  in
               if uu____67713
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____67724 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____67724 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____67738 = new_uvar "intro" env' typ'  in
                  bind uu____67738
                    (fun uu____67755  ->
                       match uu____67755 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c))
                              in
                           let uu____67779 = set_solution goal sol  in
                           bind uu____67779
                             (fun uu____67785  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                    goal.FStar_Tactics_Types.label
                                   in
                                let uu____67787 =
                                  let uu____67790 = bnorm_goal g  in
                                  replace_cur uu____67790  in
                                bind uu____67787 (fun uu____67792  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____67797 =
                 let uu____67799 = FStar_Tactics_Types.goal_env goal  in
                 let uu____67800 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____67799 uu____67800  in
               fail1 "goal is not an arrow (%s)" uu____67797)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____67685
  
let (intro_rec :
  unit -> (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder) tac) =
  fun uu____67818  ->
    let uu____67825 = cur_goal ()  in
    bind uu____67825
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____67844 =
            let uu____67851 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____67851  in
          match uu____67844 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____67864 =
                let uu____67866 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____67866  in
              if uu____67864
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____67883 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____67883
                    in
                 let bs =
                   let uu____67894 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____67894; b]  in
                 let env' =
                   let uu____67920 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____67920 bs  in
                 let uu____67921 =
                   let uu____67928 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____67928  in
                 bind uu____67921
                   (fun uu____67948  ->
                      match uu____67948 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____67962 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____67965 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____67962
                              FStar_Parser_Const.effect_Tot_lid uu____67965
                              [] FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____67983 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____67983 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____68005 =
                                   let uu____68006 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____68006.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____68005
                                  in
                               let uu____68022 = set_solution goal tm  in
                               bind uu____68022
                                 (fun uu____68031  ->
                                    let uu____68032 =
                                      let uu____68035 =
                                        bnorm_goal
                                          (let uu___1291_68038 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___1291_68038.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___1291_68038.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___1291_68038.FStar_Tactics_Types.is_guard);
                                             FStar_Tactics_Types.label =
                                               (uu___1291_68038.FStar_Tactics_Types.label)
                                           })
                                         in
                                      replace_cur uu____68035  in
                                    bind uu____68032
                                      (fun uu____68045  ->
                                         let uu____68046 =
                                           let uu____68051 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____68051, b)  in
                                         ret uu____68046)))))
          | FStar_Pervasives_Native.None  ->
              let uu____68060 =
                let uu____68062 = FStar_Tactics_Types.goal_env goal  in
                let uu____68063 = FStar_Tactics_Types.goal_type goal  in
                tts uu____68062 uu____68063  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____68060))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____68083 = cur_goal ()  in
    bind uu____68083
      (fun goal  ->
         mlog
           (fun uu____68090  ->
              let uu____68091 =
                let uu____68093 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____68093  in
              FStar_Util.print1 "norm: witness = %s\n" uu____68091)
           (fun uu____68099  ->
              let steps =
                let uu____68103 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____68103
                 in
              let t =
                let uu____68107 = FStar_Tactics_Types.goal_env goal  in
                let uu____68108 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____68107 uu____68108  in
              let uu____68109 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____68109))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____68134 =
          bind get
            (fun ps  ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
                 | g::uu____68142 -> g.FStar_Tactics_Types.opts
                 | uu____68145 -> FStar_Options.peek ()  in
               mlog
                 (fun uu____68150  ->
                    let uu____68151 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____68151)
                 (fun uu____68156  ->
                    let uu____68157 = __tc_lax e t  in
                    bind uu____68157
                      (fun uu____68178  ->
                         match uu____68178 with
                         | (t1,uu____68188,uu____68189) ->
                             let steps =
                               let uu____68193 =
                                 FStar_TypeChecker_Normalize.tr_norm_steps s
                                  in
                               FStar_List.append
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu____68193
                                in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1
                                in
                             mlog
                               (fun uu____68199  ->
                                  let uu____68200 =
                                    FStar_Syntax_Print.term_to_string t2  in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____68200)
                               (fun uu____68204  -> ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____68134
  
let (refine_intro : unit -> unit tac) =
  fun uu____68217  ->
    let uu____68220 =
      let uu____68223 = cur_goal ()  in
      bind uu____68223
        (fun g  ->
           let uu____68230 =
             let uu____68241 = FStar_Tactics_Types.goal_env g  in
             let uu____68242 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____68241
               uu____68242
              in
           match uu____68230 with
           | (uu____68245,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____68271 =
                 let uu____68276 =
                   let uu____68281 =
                     let uu____68282 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____68282]  in
                   FStar_Syntax_Subst.open_term uu____68281 phi  in
                 match uu____68276 with
                 | (bvs,phi1) ->
                     let uu____68307 =
                       let uu____68308 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____68308  in
                     (uu____68307, phi1)
                  in
               (match uu____68271 with
                | (bv1,phi1) ->
                    let uu____68327 =
                      let uu____68330 = FStar_Tactics_Types.goal_env g  in
                      let uu____68331 =
                        let uu____68332 =
                          let uu____68335 =
                            let uu____68336 =
                              let uu____68343 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____68343)  in
                            FStar_Syntax_Syntax.NT uu____68336  in
                          [uu____68335]  in
                        FStar_Syntax_Subst.subst uu____68332 phi1  in
                      mk_irrelevant_goal "refine_intro refinement"
                        uu____68330 uu____68331 g.FStar_Tactics_Types.opts
                        g.FStar_Tactics_Types.label
                       in
                    bind uu____68327
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____68352  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____68220
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____68375 = cur_goal ()  in
      bind uu____68375
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____68384 = FStar_Tactics_Types.goal_env goal  in
               let uu____68385 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____68384 uu____68385
             else FStar_Tactics_Types.goal_env goal  in
           let uu____68388 = __tc env t  in
           bind uu____68388
             (fun uu____68407  ->
                match uu____68407 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____68422  ->
                         let uu____68423 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____68425 =
                           let uu____68427 =
                             FStar_Tactics_Types.goal_env goal  in
                           FStar_TypeChecker_Rel.guard_to_string uu____68427
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____68423 uu____68425)
                      (fun uu____68431  ->
                         let uu____68432 =
                           let uu____68435 =
                             FStar_Tactics_Types.goal_env goal  in
                           proc_guard "__exact typing" uu____68435 guard  in
                         bind uu____68432
                           (fun uu____68438  ->
                              mlog
                                (fun uu____68442  ->
                                   let uu____68443 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____68445 =
                                     let uu____68447 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____68447
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____68443 uu____68445)
                                (fun uu____68451  ->
                                   let uu____68452 =
                                     let uu____68456 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____68457 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____68456 typ uu____68457  in
                                   bind uu____68452
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____68467 =
                                             let uu____68469 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____68469 t1  in
                                           let uu____68470 =
                                             let uu____68472 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____68472 typ  in
                                           let uu____68473 =
                                             let uu____68475 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____68476 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____68475 uu____68476  in
                                           let uu____68477 =
                                             let uu____68479 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____68480 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____68479 uu____68480  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____68467 uu____68470
                                             uu____68473 uu____68477)))))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun try_refine  ->
    fun set_expected_typ1  ->
      fun tm  ->
        let uu____68506 =
          mlog
            (fun uu____68511  ->
               let uu____68512 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____68512)
            (fun uu____68517  ->
               let uu____68518 =
                 let uu____68525 = __exact_now set_expected_typ1 tm  in
                 catch uu____68525  in
               bind uu____68518
                 (fun uu___611_68534  ->
                    match uu___611_68534 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        traise e
                    | FStar_Util.Inl e ->
                        mlog
                          (fun uu____68545  ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____68549  ->
                             let uu____68550 =
                               let uu____68557 =
                                 let uu____68560 =
                                   norm [FStar_Syntax_Embeddings.Delta]  in
                                 bind uu____68560
                                   (fun uu____68565  ->
                                      let uu____68566 = refine_intro ()  in
                                      bind uu____68566
                                        (fun uu____68570  ->
                                           __exact_now set_expected_typ1 tm))
                                  in
                               catch uu____68557  in
                             bind uu____68550
                               (fun uu___610_68577  ->
                                  match uu___610_68577 with
                                  | FStar_Util.Inr r ->
                                      mlog
                                        (fun uu____68586  ->
                                           FStar_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu____68589  -> ret ())
                                  | FStar_Util.Inl uu____68590 ->
                                      mlog
                                        (fun uu____68592  ->
                                           FStar_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu____68595  -> traise e)))))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____68506
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____68647 = f x  in
          bind uu____68647
            (fun y  ->
               let uu____68655 = mapM f xs  in
               bind uu____68655 (fun ys  -> ret (y :: ys)))
  
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
          let uu____68727 = do_unify e ty1 ty2  in
          bind uu____68727
            (fun uu___612_68741  ->
               if uu___612_68741
               then ret acc
               else
                 (let uu____68761 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____68761 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____68782 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____68784 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____68782
                        uu____68784
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____68801 =
                        let uu____68803 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____68803  in
                      if uu____68801
                      then fail "Codomain is effectful"
                      else
                        (let uu____68827 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____68827
                           (fun uu____68854  ->
                              match uu____68854 with
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
      let uu____68944 =
        mlog
          (fun uu____68949  ->
             let uu____68950 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_apply: tm = %s\n" uu____68950)
          (fun uu____68955  ->
             let uu____68956 = cur_goal ()  in
             bind uu____68956
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____68964 = __tc e tm  in
                  bind uu____68964
                    (fun uu____68985  ->
                       match uu____68985 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____68998 =
                             let uu____69009 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____69009  in
                           bind uu____68998
                             (fun uvs  ->
                                let fix_qual q =
                                  match q with
                                  | FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Meta uu____69047)
                                      ->
                                      FStar_Pervasives_Native.Some
                                        (FStar_Syntax_Syntax.Implicit false)
                                  | uu____69051 -> q  in
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____69074  ->
                                       fun w  ->
                                         match uu____69074 with
                                         | (uvt,q,uu____69092) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, (fix_qual q))]) uvs tm1
                                   in
                                let uvset =
                                  let uu____69124 =
                                    FStar_Syntax_Free.new_uv_set ()  in
                                  FStar_List.fold_right
                                    (fun uu____69141  ->
                                       fun s  ->
                                         match uu____69141 with
                                         | (uu____69153,uu____69154,uv) ->
                                             let uu____69156 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                in
                                             FStar_Util.set_union s
                                               uu____69156) uvs uu____69124
                                   in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset  in
                                let uu____69166 = solve' goal w  in
                                bind uu____69166
                                  (fun uu____69171  ->
                                     let uu____69172 =
                                       mapM
                                         (fun uu____69189  ->
                                            match uu____69189 with
                                            | (uvt,q,uv) ->
                                                let uu____69201 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                   in
                                                (match uu____69201 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____69206 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____69207 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv)
                                                        in
                                                     if uu____69207
                                                     then ret ()
                                                     else
                                                       (let uu____69214 =
                                                          let uu____69217 =
                                                            bnorm_goal
                                                              (let uu___1452_69220
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___1452_69220.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___1452_69220.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false;
                                                                 FStar_Tactics_Types.label
                                                                   =
                                                                   (uu___1452_69220.FStar_Tactics_Types.label)
                                                               })
                                                             in
                                                          [uu____69217]  in
                                                        add_goals uu____69214)))
                                         uvs
                                        in
                                     bind uu____69172
                                       (fun uu____69225  ->
                                          proc_guard "apply guard" e guard))))))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____68944
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____69253 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____69253
    then
      let uu____69262 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____69277 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____69330 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____69262 with
      | (pre,post) ->
          let post1 =
            let uu____69363 =
              let uu____69374 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____69374]  in
            FStar_Syntax_Util.mk_app post uu____69363  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____69405 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____69405
       then
         let uu____69414 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____69414
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
            let uu____69493 = f x e  in
            bind uu____69493 (fun e'  -> fold_left f e' xs1)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____69508 =
      let uu____69511 =
        bind get
          (fun ps  ->
             mlog
               (fun uu____69518  ->
                  let uu____69519 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____69519)
               (fun uu____69525  ->
                  let is_unit_t t =
                    let uu____69533 =
                      let uu____69534 = FStar_Syntax_Subst.compress t  in
                      uu____69534.FStar_Syntax_Syntax.n  in
                    match uu____69533 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____69540 -> false  in
                  let uu____69542 = cur_goal ()  in
                  bind uu____69542
                    (fun goal  ->
                       let uu____69548 =
                         let uu____69557 = FStar_Tactics_Types.goal_env goal
                            in
                         __tc uu____69557 tm  in
                       bind uu____69548
                         (fun uu____69572  ->
                            match uu____69572 with
                            | (tm1,t,guard) ->
                                let uu____69584 =
                                  FStar_Syntax_Util.arrow_formals_comp t  in
                                (match uu____69584 with
                                 | (bs,comp) ->
                                     let uu____69617 = lemma_or_sq comp  in
                                     (match uu____69617 with
                                      | FStar_Pervasives_Native.None  ->
                                          fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre,post) ->
                                          let uu____69637 =
                                            fold_left
                                              (fun uu____69699  ->
                                                 fun uu____69700  ->
                                                   match (uu____69699,
                                                           uu____69700)
                                                   with
                                                   | ((b,aq),(uvs,imps,subst1))
                                                       ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst1
                                                           b.FStar_Syntax_Syntax.sort
                                                          in
                                                       let uu____69851 =
                                                         is_unit_t b_t  in
                                                       if uu____69851
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
                                                         (let uu____69974 =
                                                            let uu____69981 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            new_uvar
                                                              "apply_lemma"
                                                              uu____69981 b_t
                                                             in
                                                          bind uu____69974
                                                            (fun uu____70012 
                                                               ->
                                                               match uu____70012
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
                                          bind uu____69637
                                            (fun uu____70198  ->
                                               match uu____70198 with
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
                                                   let uu____70286 =
                                                     let uu____70290 =
                                                       FStar_Tactics_Types.goal_env
                                                         goal
                                                        in
                                                     let uu____70291 =
                                                       FStar_Syntax_Util.mk_squash
                                                         FStar_Syntax_Syntax.U_zero
                                                         post1
                                                        in
                                                     let uu____70292 =
                                                       FStar_Tactics_Types.goal_type
                                                         goal
                                                        in
                                                     do_unify uu____70290
                                                       uu____70291
                                                       uu____70292
                                                      in
                                                   bind uu____70286
                                                     (fun b  ->
                                                        if
                                                          Prims.op_Negation b
                                                        then
                                                          let uu____70303 =
                                                            let uu____70305 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            tts uu____70305
                                                              tm1
                                                             in
                                                          let uu____70306 =
                                                            let uu____70308 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            let uu____70309 =
                                                              FStar_Syntax_Util.mk_squash
                                                                FStar_Syntax_Syntax.U_zero
                                                                post1
                                                               in
                                                            tts uu____70308
                                                              uu____70309
                                                             in
                                                          let uu____70310 =
                                                            let uu____70312 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            let uu____70313 =
                                                              FStar_Tactics_Types.goal_type
                                                                goal
                                                               in
                                                            tts uu____70312
                                                              uu____70313
                                                             in
                                                          fail3
                                                            "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                            uu____70303
                                                            uu____70306
                                                            uu____70310
                                                        else
                                                          (let uu____70317 =
                                                             solve' goal
                                                               FStar_Syntax_Util.exp_unit
                                                              in
                                                           bind uu____70317
                                                             (fun uu____70325
                                                                 ->
                                                                let is_free_uvar
                                                                  uv t1 =
                                                                  let free_uvars
                                                                    =
                                                                    let uu____70351
                                                                    =
                                                                    let uu____70354
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____70354
                                                                     in
                                                                    FStar_List.map
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____70351
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
                                                                    let uu____70390
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____70390)
                                                                    goals
                                                                   in
                                                                let checkone
                                                                  t1 goals =
                                                                  let uu____70407
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                  match uu____70407
                                                                  with
                                                                  | (hd1,uu____70426)
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____70453)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____70470
                                                                    -> false)
                                                                   in
                                                                let uu____70472
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
                                                                    let uu____70515
                                                                    = imp  in
                                                                    match uu____70515
                                                                    with
                                                                    | 
                                                                    (term,ctx_uvar)
                                                                    ->
                                                                    let uu____70526
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____70526
                                                                    with
                                                                    | 
                                                                    (hd1,uu____70548)
                                                                    ->
                                                                    let uu____70573
                                                                    =
                                                                    let uu____70574
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____70574.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____70573
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____70582)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___1562_70602
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___1562_70602.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___1562_70602.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___1562_70602.FStar_Tactics_Types.is_guard);
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___1562_70602.FStar_Tactics_Types.label)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____70605
                                                                    ->
                                                                    mlog
                                                                    (fun
                                                                    uu____70611
                                                                     ->
                                                                    let uu____70612
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                                                     in
                                                                    let uu____70614
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____70612
                                                                    uu____70614)
                                                                    (fun
                                                                    uu____70621
                                                                     ->
                                                                    let env =
                                                                    let uu___1567_70623
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___1567_70623.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1567_70623.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1567_70623.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___1567_70623.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1567_70623.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1567_70623.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1567_70623.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1567_70623.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___1567_70623.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___1567_70623.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___1567_70623.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1567_70623.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1567_70623.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1567_70623.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1567_70623.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1567_70623.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1567_70623.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1567_70623.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___1567_70623.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___1567_70623.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___1567_70623.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1567_70623.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1567_70623.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1567_70623.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1567_70623.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1567_70623.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1567_70623.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1567_70623.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1567_70623.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1567_70623.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1567_70623.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1567_70623.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1567_70623.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1567_70623.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___1567_70623.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1567_70623.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1567_70623.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___1567_70623.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1567_70623.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1567_70623.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1567_70623.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1567_70623.FStar_TypeChecker_Env.nbe)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let uu____70626
                                                                    =
                                                                    let uu____70629
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____70633
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
                                                                    let uu____70635
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____70633
                                                                    uu____70635
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____70641
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    uu____70629
                                                                    uu____70641
                                                                    g_typ  in
                                                                    bind
                                                                    uu____70626
                                                                    (fun
                                                                    uu____70645
                                                                     ->
                                                                    ret []))))))
                                                                   in
                                                                bind
                                                                  uu____70472
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
                                                                    let uu____70709
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____70709
                                                                    then
                                                                    let uu____70714
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____70714
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
                                                                    let uu____70729
                                                                    =
                                                                    let uu____70731
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____70731
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____70729)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____70732
                                                                    =
                                                                    let uu____70735
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____70735
                                                                    guard  in
                                                                    bind
                                                                    uu____70732
                                                                    (fun
                                                                    uu____70739
                                                                     ->
                                                                    let uu____70740
                                                                    =
                                                                    let uu____70743
                                                                    =
                                                                    let uu____70745
                                                                    =
                                                                    let uu____70747
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____70748
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____70747
                                                                    uu____70748
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____70745
                                                                     in
                                                                    if
                                                                    uu____70743
                                                                    then
                                                                    let uu____70752
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____70752
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    goal.FStar_Tactics_Types.label
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____70740
                                                                    (fun
                                                                    uu____70757
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2)))))))))))))
         in
      focus uu____69511  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____69508
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____70781 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____70781 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____70791::(e1,uu____70793)::(e2,uu____70795)::[])) when
        (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) ||
          (FStar_Ident.lid_equals l FStar_Parser_Const.c_eq2_lid)
        -> FStar_Pervasives_Native.Some (e1, e2)
    | uu____70856 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____70881 = destruct_eq' typ  in
    match uu____70881 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____70911 = FStar_Syntax_Util.un_squash typ  in
        (match uu____70911 with
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
        let uu____70980 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____70980 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', bv', [])
            else
              (let uu____71038 = aux e'  in
               FStar_Util.map_opt uu____71038
                 (fun uu____71069  ->
                    match uu____71069 with
                    | (e'',bv,bvs) -> (e'', bv, (bv' :: bvs))))
         in
      let uu____71095 = aux e  in
      FStar_Util.map_opt uu____71095
        (fun uu____71126  ->
           match uu____71126 with
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
          let uu____71200 =
            let uu____71211 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____71211  in
          FStar_Util.map_opt uu____71200
            (fun uu____71229  ->
               match uu____71229 with
               | (e0,b11,bvs) ->
                   let s1 bv =
                     let uu___1640_71251 = bv  in
                     let uu____71252 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___1640_71251.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___1640_71251.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____71252
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___1644_71260 =
                       g.FStar_Tactics_Types.goal_ctx_uvar  in
                     let uu____71261 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____71270 =
                       let uu____71273 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____71273  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___1644_71260.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____71261;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____71270;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___1644_71260.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___1644_71260.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___1644_71260.FStar_Syntax_Syntax.ctx_uvar_range);
                       FStar_Syntax_Syntax.ctx_uvar_meta =
                         (uu___1644_71260.FStar_Syntax_Syntax.ctx_uvar_meta)
                     }  in
                   let uu___1647_71274 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1647_71274.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___1647_71274.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___1647_71274.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1647_71274.FStar_Tactics_Types.label)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____71285 =
      let uu____71288 = cur_goal ()  in
      bind uu____71288
        (fun goal  ->
           let uu____71296 = h  in
           match uu____71296 with
           | (bv,uu____71300) ->
               mlog
                 (fun uu____71308  ->
                    let uu____71309 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____71311 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____71309
                      uu____71311)
                 (fun uu____71316  ->
                    let uu____71317 =
                      let uu____71328 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____71328  in
                    match uu____71317 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                        let uu____71355 =
                          destruct_eq bv1.FStar_Syntax_Syntax.sort  in
                        (match uu____71355 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____71370 =
                               let uu____71371 =
                                 FStar_Syntax_Subst.compress x  in
                               uu____71371.FStar_Syntax_Syntax.n  in
                             (match uu____71370 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv2 =
                                    let uu___1670_71388 = bv2  in
                                    let uu____71389 =
                                      FStar_Syntax_Subst.subst s
                                        bv2.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1670_71388.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1670_71388.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____71389
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv1 :: bvs1)  in
                                  let new_goal =
                                    let uu___1674_71397 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____71398 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____71407 =
                                      let uu____71410 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____71410
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___1674_71397.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____71398;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____71407;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___1674_71397.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___1674_71397.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___1674_71397.FStar_Syntax_Syntax.ctx_uvar_range);
                                      FStar_Syntax_Syntax.ctx_uvar_meta =
                                        (uu___1674_71397.FStar_Syntax_Syntax.ctx_uvar_meta)
                                    }  in
                                  replace_cur
                                    (let uu___1677_71413 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___1677_71413.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___1677_71413.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___1677_71413.FStar_Tactics_Types.is_guard);
                                       FStar_Tactics_Types.label =
                                         (uu___1677_71413.FStar_Tactics_Types.label)
                                     })
                              | uu____71414 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____71416 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____71285
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____71446 =
        let uu____71449 = cur_goal ()  in
        bind uu____71449
          (fun goal  ->
             let uu____71460 = b  in
             match uu____71460 with
             | (bv,uu____71464) ->
                 let bv' =
                   let uu____71470 =
                     let uu___1688_71471 = bv  in
                     let uu____71472 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____71472;
                       FStar_Syntax_Syntax.index =
                         (uu___1688_71471.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___1688_71471.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____71470  in
                 let s1 =
                   let uu____71477 =
                     let uu____71478 =
                       let uu____71485 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____71485)  in
                     FStar_Syntax_Syntax.NT uu____71478  in
                   [uu____71477]  in
                 let uu____71490 = subst_goal bv bv' s1 goal  in
                 (match uu____71490 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____71446
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____71512 =
      let uu____71515 = cur_goal ()  in
      bind uu____71515
        (fun goal  ->
           let uu____71524 = b  in
           match uu____71524 with
           | (bv,uu____71528) ->
               let uu____71533 =
                 let uu____71544 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____71544  in
               (match uu____71533 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                    let uu____71571 = FStar_Syntax_Util.type_u ()  in
                    (match uu____71571 with
                     | (ty,u) ->
                         let uu____71580 = new_uvar "binder_retype" e0 ty  in
                         bind uu____71580
                           (fun uu____71599  ->
                              match uu____71599 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___1712_71609 = bv1  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1712_71609.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1712_71609.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____71613 =
                                      let uu____71614 =
                                        let uu____71621 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv1, uu____71621)  in
                                      FStar_Syntax_Syntax.NT uu____71614  in
                                    [uu____71613]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___1717_71633 = b1  in
                                         let uu____71634 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___1717_71633.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___1717_71633.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____71634
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____71641  ->
                                       let new_goal =
                                         let uu____71643 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____71644 =
                                           let uu____71645 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____71645
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____71643 uu____71644
                                          in
                                       let uu____71646 = add_goals [new_goal]
                                          in
                                       bind uu____71646
                                         (fun uu____71651  ->
                                            let uu____71652 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv1.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____71652
                                              goal.FStar_Tactics_Types.opts
                                              goal.FStar_Tactics_Types.label))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____71512
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____71678 =
        let uu____71681 = cur_goal ()  in
        bind uu____71681
          (fun goal  ->
             let uu____71690 = b  in
             match uu____71690 with
             | (bv,uu____71694) ->
                 let uu____71699 =
                   let uu____71710 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____71710  in
                 (match uu____71699 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                      let steps =
                        let uu____71740 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____71740
                         in
                      let sort' =
                        normalize steps e0 bv1.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___1738_71745 = bv1  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___1738_71745.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___1738_71745.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____71747 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____71747))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____71678
  
let (revert : unit -> unit tac) =
  fun uu____71760  ->
    let uu____71763 = cur_goal ()  in
    bind uu____71763
      (fun goal  ->
         let uu____71769 =
           let uu____71776 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____71776  in
         match uu____71769 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____71793 =
                 let uu____71796 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____71796  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____71793
                in
             let uu____71811 = new_uvar "revert" env' typ'  in
             bind uu____71811
               (fun uu____71827  ->
                  match uu____71827 with
                  | (r,u_r) ->
                      let uu____71836 =
                        let uu____71839 =
                          let uu____71840 =
                            let uu____71841 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____71841.FStar_Syntax_Syntax.pos  in
                          let uu____71844 =
                            let uu____71849 =
                              let uu____71850 =
                                let uu____71859 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____71859  in
                              [uu____71850]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____71849  in
                          uu____71844 FStar_Pervasives_Native.None
                            uu____71840
                           in
                        set_solution goal uu____71839  in
                      bind uu____71836
                        (fun uu____71878  ->
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
      let uu____71892 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____71892
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____71908 = cur_goal ()  in
    bind uu____71908
      (fun goal  ->
         mlog
           (fun uu____71916  ->
              let uu____71917 = FStar_Syntax_Print.binder_to_string b  in
              let uu____71919 =
                let uu____71921 =
                  let uu____71923 =
                    let uu____71932 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____71932  in
                  FStar_All.pipe_right uu____71923 FStar_List.length  in
                FStar_All.pipe_right uu____71921 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____71917 uu____71919)
           (fun uu____71953  ->
              let uu____71954 =
                let uu____71965 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____71965  in
              match uu____71954 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bv1,bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____72010 =
                          free_in bv1 bv'.FStar_Syntax_Syntax.sort  in
                        if uu____72010
                        then
                          let uu____72015 =
                            let uu____72017 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____72017
                             in
                          fail uu____72015
                        else check1 bvs2
                     in
                  let uu____72022 =
                    let uu____72024 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv1 uu____72024  in
                  if uu____72022
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____72031 = check1 bvs  in
                     bind uu____72031
                       (fun uu____72037  ->
                          let env' = push_bvs e' bvs  in
                          let uu____72039 =
                            let uu____72046 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____72046  in
                          bind uu____72039
                            (fun uu____72056  ->
                               match uu____72056 with
                               | (ut,uvar_ut) ->
                                   let uu____72065 = set_solution goal ut  in
                                   bind uu____72065
                                     (fun uu____72070  ->
                                        let uu____72071 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                            goal.FStar_Tactics_Types.label
                                           in
                                        replace_cur uu____72071))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____72079  ->
    let uu____72082 = cur_goal ()  in
    bind uu____72082
      (fun goal  ->
         let uu____72088 =
           let uu____72095 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____72095  in
         match uu____72088 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____72104) ->
             let uu____72109 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____72109)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____72122 = cur_goal ()  in
    bind uu____72122
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____72132 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____72132  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____72135  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____72148 = cur_goal ()  in
    bind uu____72148
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____72158 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____72158  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____72161  -> add_goals [g']))
  
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
            let uu____72202 = FStar_Syntax_Subst.compress t  in
            uu____72202.FStar_Syntax_Syntax.n  in
          let uu____72205 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___1922_72212 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___1922_72212.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___1922_72212.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____72205
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____72229 =
                   let uu____72230 = FStar_Syntax_Subst.compress t1  in
                   uu____72230.FStar_Syntax_Syntax.n  in
                 match uu____72229 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____72261 = ff hd1  in
                     bind uu____72261
                       (fun hd2  ->
                          let fa uu____72287 =
                            match uu____72287 with
                            | (a,q) ->
                                let uu____72308 = ff a  in
                                bind uu____72308 (fun a1  -> ret (a1, q))
                             in
                          let uu____72327 = mapM fa args  in
                          bind uu____72327
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____72409 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____72409 with
                      | (bs1,t') ->
                          let uu____72418 =
                            let uu____72421 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____72421 t'  in
                          bind uu____72418
                            (fun t''  ->
                               let uu____72425 =
                                 let uu____72426 =
                                   let uu____72445 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____72454 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____72445, uu____72454, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____72426  in
                               ret uu____72425))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____72529 = ff hd1  in
                     bind uu____72529
                       (fun hd2  ->
                          let ffb br =
                            let uu____72544 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____72544 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____72576 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____72576  in
                                let uu____72577 = ff1 e  in
                                bind uu____72577
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____72592 = mapM ffb brs  in
                          bind uu____72592
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____72636;
                          FStar_Syntax_Syntax.lbtyp = uu____72637;
                          FStar_Syntax_Syntax.lbeff = uu____72638;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____72640;
                          FStar_Syntax_Syntax.lbpos = uu____72641;_}::[]),e)
                     ->
                     let lb =
                       let uu____72669 =
                         let uu____72670 = FStar_Syntax_Subst.compress t1  in
                         uu____72670.FStar_Syntax_Syntax.n  in
                       match uu____72669 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____72674) -> lb
                       | uu____72690 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____72700 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____72700
                         (fun def1  ->
                            ret
                              (let uu___1875_72706 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1875_72706.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1875_72706.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1875_72706.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1875_72706.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1875_72706.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1875_72706.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____72707 = fflb lb  in
                     bind uu____72707
                       (fun lb1  ->
                          let uu____72717 =
                            let uu____72722 =
                              let uu____72723 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____72723]  in
                            FStar_Syntax_Subst.open_term uu____72722 e  in
                          match uu____72717 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____72753 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____72753  in
                              let uu____72754 = ff1 e1  in
                              bind uu____72754
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____72801 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____72801
                         (fun def  ->
                            ret
                              (let uu___1893_72807 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1893_72807.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1893_72807.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1893_72807.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1893_72807.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1893_72807.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1893_72807.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____72808 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____72808 with
                      | (lbs1,e1) ->
                          let uu____72823 = mapM fflb lbs1  in
                          bind uu____72823
                            (fun lbs2  ->
                               let uu____72835 = ff e1  in
                               bind uu____72835
                                 (fun e2  ->
                                    let uu____72843 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____72843 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____72914 = ff t2  in
                     bind uu____72914
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____72945 = ff t2  in
                     bind uu____72945
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____72952 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___1917_72959 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___1917_72959.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___1917_72959.FStar_Syntax_Syntax.vars)
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
              let uu____73006 =
                FStar_TypeChecker_TcTerm.tc_term
                  (let uu___1930_73015 = env  in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___1930_73015.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___1930_73015.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___1930_73015.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___1930_73015.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_sig =
                       (uu___1930_73015.FStar_TypeChecker_Env.gamma_sig);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___1930_73015.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___1930_73015.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___1930_73015.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___1930_73015.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.attrtab =
                       (uu___1930_73015.FStar_TypeChecker_Env.attrtab);
                     FStar_TypeChecker_Env.is_pattern =
                       (uu___1930_73015.FStar_TypeChecker_Env.is_pattern);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___1930_73015.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___1930_73015.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___1930_73015.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___1930_73015.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___1930_73015.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___1930_73015.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___1930_73015.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___1930_73015.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___1930_73015.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax = true;
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___1930_73015.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.phase1 =
                       (uu___1930_73015.FStar_TypeChecker_Env.phase1);
                     FStar_TypeChecker_Env.failhard =
                       (uu___1930_73015.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___1930_73015.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.uvar_subtyping =
                       (uu___1930_73015.FStar_TypeChecker_Env.uvar_subtyping);
                     FStar_TypeChecker_Env.tc_term =
                       (uu___1930_73015.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.type_of =
                       (uu___1930_73015.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___1930_73015.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.check_type_of =
                       (uu___1930_73015.FStar_TypeChecker_Env.check_type_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___1930_73015.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (uu___1930_73015.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (uu___1930_73015.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.fv_delta_depths =
                       (uu___1930_73015.FStar_TypeChecker_Env.fv_delta_depths);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___1930_73015.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (uu___1930_73015.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.splice =
                       (uu___1930_73015.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.postprocess =
                       (uu___1930_73015.FStar_TypeChecker_Env.postprocess);
                     FStar_TypeChecker_Env.is_native_tactic =
                       (uu___1930_73015.FStar_TypeChecker_Env.is_native_tactic);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___1930_73015.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (uu___1930_73015.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (uu___1930_73015.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.nbe =
                       (uu___1930_73015.FStar_TypeChecker_Env.nbe)
                   }) t
                 in
              match uu____73006 with
              | (t1,lcomp,g) ->
                  let uu____73022 =
                    (let uu____73026 =
                       FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                     Prims.op_Negation uu____73026) ||
                      (let uu____73029 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____73029)
                     in
                  if uu____73022
                  then ret t1
                  else
                    (let rewrite_eq =
                       let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                       let uu____73040 = new_uvar "pointwise_rec" env typ  in
                       bind uu____73040
                         (fun uu____73057  ->
                            match uu____73057 with
                            | (ut,uvar_ut) ->
                                (log ps
                                   (fun uu____73070  ->
                                      let uu____73071 =
                                        FStar_Syntax_Print.term_to_string t1
                                         in
                                      let uu____73073 =
                                        FStar_Syntax_Print.term_to_string ut
                                         in
                                      FStar_Util.print2
                                        "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                        uu____73071 uu____73073);
                                 (let uu____73076 =
                                    let uu____73079 =
                                      let uu____73080 =
                                        FStar_TypeChecker_TcTerm.universe_of
                                          env typ
                                         in
                                      FStar_Syntax_Util.mk_eq2 uu____73080
                                        typ t1 ut
                                       in
                                    add_irrelevant_goal
                                      "pointwise_rec equation" env
                                      uu____73079 opts label1
                                     in
                                  bind uu____73076
                                    (fun uu____73084  ->
                                       let uu____73085 =
                                         bind tau
                                           (fun uu____73091  ->
                                              let ut1 =
                                                FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                  env ut
                                                 in
                                              log ps
                                                (fun uu____73097  ->
                                                   let uu____73098 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1
                                                      in
                                                   let uu____73100 =
                                                     FStar_Syntax_Print.term_to_string
                                                       ut1
                                                      in
                                                   FStar_Util.print2
                                                     "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                     uu____73098 uu____73100);
                                              ret ut1)
                                          in
                                       focus uu____73085))))
                        in
                     let uu____73103 = catch rewrite_eq  in
                     bind uu____73103
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
          let uu____73315 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____73315
            (fun t1  ->
               let uu____73323 =
                 f env
                   (let uu___2007_73331 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___2007_73331.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___2007_73331.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____73323
                 (fun uu____73347  ->
                    match uu____73347 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____73370 =
                               let uu____73371 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____73371.FStar_Syntax_Syntax.n  in
                             match uu____73370 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____73408 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____73408
                                   (fun uu____73430  ->
                                      match uu____73430 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____73446 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____73446
                                            (fun uu____73470  ->
                                               match uu____73470 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___1987_73500 =
                                                         t3  in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___1987_73500.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___1987_73500.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____73542 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____73542 with
                                  | (bs1,t') ->
                                      let uu____73557 =
                                        let uu____73564 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____73564 ctrl1 t'
                                         in
                                      bind uu____73557
                                        (fun uu____73579  ->
                                           match uu____73579 with
                                           | (t'',ctrl2) ->
                                               let uu____73594 =
                                                 let uu____73601 =
                                                   let uu___2000_73604 = t4
                                                      in
                                                   let uu____73607 =
                                                     let uu____73608 =
                                                       let uu____73627 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____73636 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____73627,
                                                         uu____73636, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____73608
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____73607;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___2000_73604.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___2000_73604.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____73601, ctrl2)  in
                                               ret uu____73594))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____73689 -> ret (t3, ctrl1))))

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
              let uu____73735 = ctrl_tac_fold f env ctrl t  in
              bind uu____73735
                (fun uu____73756  ->
                   match uu____73756 with
                   | (t1,ctrl1) ->
                       let uu____73771 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____73771
                         (fun uu____73795  ->
                            match uu____73795 with
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
                let uu____73886 =
                  let uu____73894 =
                    add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                      opts label1
                     in
                  bind uu____73894
                    (fun uu____73905  ->
                       let uu____73906 = ctrl t1  in
                       bind uu____73906
                         (fun res  ->
                            let uu____73932 = trivial ()  in
                            bind uu____73932 (fun uu____73941  -> ret res)))
                   in
                bind uu____73886
                  (fun uu____73959  ->
                     match uu____73959 with
                     | (should_rewrite,ctrl1) ->
                         if Prims.op_Negation should_rewrite
                         then ret (t1, ctrl1)
                         else
                           (let uu____73988 =
                              FStar_TypeChecker_TcTerm.tc_term
                                (let uu___2037_73997 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___2037_73997.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___2037_73997.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___2037_73997.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___2037_73997.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___2037_73997.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___2037_73997.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___2037_73997.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___2037_73997.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___2037_73997.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___2037_73997.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___2037_73997.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___2037_73997.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___2037_73997.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___2037_73997.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___2037_73997.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___2037_73997.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___2037_73997.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___2037_73997.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___2037_73997.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___2037_73997.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___2037_73997.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___2037_73997.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___2037_73997.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___2037_73997.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___2037_73997.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___2037_73997.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___2037_73997.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___2037_73997.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___2037_73997.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___2037_73997.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___2037_73997.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___2037_73997.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___2037_73997.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___2037_73997.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___2037_73997.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___2037_73997.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___2037_73997.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___2037_73997.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___2037_73997.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___2037_73997.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___2037_73997.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___2037_73997.FStar_TypeChecker_Env.nbe)
                                 }) t1
                               in
                            match uu____73988 with
                            | (t2,lcomp,g) ->
                                let uu____74008 =
                                  (let uu____74012 =
                                     FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                       lcomp
                                      in
                                   Prims.op_Negation uu____74012) ||
                                    (let uu____74015 =
                                       FStar_TypeChecker_Env.is_trivial g  in
                                     Prims.op_Negation uu____74015)
                                   in
                                if uu____74008
                                then ret (t2, globalStop)
                                else
                                  (let typ =
                                     lcomp.FStar_Syntax_Syntax.res_typ  in
                                   let uu____74031 =
                                     new_uvar "pointwise_rec" env typ  in
                                   bind uu____74031
                                     (fun uu____74052  ->
                                        match uu____74052 with
                                        | (ut,uvar_ut) ->
                                            (log ps
                                               (fun uu____74069  ->
                                                  let uu____74070 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t2
                                                     in
                                                  let uu____74072 =
                                                    FStar_Syntax_Print.term_to_string
                                                      ut
                                                     in
                                                  FStar_Util.print2
                                                    "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                    uu____74070 uu____74072);
                                             (let uu____74075 =
                                                let uu____74078 =
                                                  let uu____74079 =
                                                    FStar_TypeChecker_TcTerm.universe_of
                                                      env typ
                                                     in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____74079 typ t2 ut
                                                   in
                                                add_irrelevant_goal
                                                  "rewrite_rec equation" env
                                                  uu____74078 opts label1
                                                 in
                                              bind uu____74075
                                                (fun uu____74087  ->
                                                   let uu____74088 =
                                                     bind rewriter
                                                       (fun uu____74102  ->
                                                          let ut1 =
                                                            FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                              env ut
                                                             in
                                                          log ps
                                                            (fun uu____74108 
                                                               ->
                                                               let uu____74109
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   t2
                                                                  in
                                                               let uu____74111
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   ut1
                                                                  in
                                                               FStar_Util.print2
                                                                 "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                                 uu____74109
                                                                 uu____74111);
                                                          ret (ut1, ctrl1))
                                                      in
                                                   focus uu____74088)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term -> (Prims.bool * FStar_BigInt.t) tac) ->
    unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____74156 =
        bind get
          (fun ps  ->
             let uu____74166 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____74166 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____74204  ->
                       let uu____74205 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____74205);
                  bind dismiss_all
                    (fun uu____74210  ->
                       let uu____74211 =
                         let uu____74218 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____74218
                           keepGoing gt1
                          in
                       bind uu____74211
                         (fun uu____74228  ->
                            match uu____74228 with
                            | (gt',uu____74236) ->
                                (log ps
                                   (fun uu____74240  ->
                                      let uu____74241 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____74241);
                                 (let uu____74244 = push_goals gs  in
                                  bind uu____74244
                                    (fun uu____74249  ->
                                       let uu____74250 =
                                         let uu____74253 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____74253]  in
                                       add_goals uu____74250)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____74156
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____74278 =
        bind get
          (fun ps  ->
             let uu____74288 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____74288 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____74326  ->
                       let uu____74327 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____74327);
                  bind dismiss_all
                    (fun uu____74332  ->
                       let uu____74333 =
                         let uu____74336 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____74336 gt1
                          in
                       bind uu____74333
                         (fun gt'  ->
                            log ps
                              (fun uu____74344  ->
                                 let uu____74345 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____74345);
                            (let uu____74348 = push_goals gs  in
                             bind uu____74348
                               (fun uu____74353  ->
                                  let uu____74354 =
                                    let uu____74357 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____74357]  in
                                  add_goals uu____74354))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____74278
  
let (trefl : unit -> unit tac) =
  fun uu____74370  ->
    let uu____74373 =
      let uu____74376 = cur_goal ()  in
      bind uu____74376
        (fun g  ->
           let uu____74394 =
             let uu____74399 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____74399  in
           match uu____74394 with
           | FStar_Pervasives_Native.Some t ->
               let uu____74407 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____74407 with
                | (hd1,args) ->
                    let uu____74446 =
                      let uu____74459 =
                        let uu____74460 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____74460.FStar_Syntax_Syntax.n  in
                      (uu____74459, args)  in
                    (match uu____74446 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____74474::(l,uu____74476)::(r,uu____74478)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____74525 =
                           let uu____74529 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____74529 l r  in
                         bind uu____74525
                           (fun b  ->
                              if b
                              then solve' g FStar_Syntax_Util.exp_unit
                              else
                                (let l1 =
                                   let uu____74540 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____74540 l
                                    in
                                 let r1 =
                                   let uu____74542 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____74542 r
                                    in
                                 let uu____74543 =
                                   let uu____74547 =
                                     FStar_Tactics_Types.goal_env g  in
                                   do_unify uu____74547 l1 r1  in
                                 bind uu____74543
                                   (fun b1  ->
                                      if b1
                                      then
                                        solve' g FStar_Syntax_Util.exp_unit
                                      else
                                        (let uu____74557 =
                                           let uu____74559 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____74559 l1  in
                                         let uu____74560 =
                                           let uu____74562 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____74562 r1  in
                                         fail2
                                           "not a trivial equality ((%s) vs (%s))"
                                           uu____74557 uu____74560))))
                     | (hd2,uu____74565) ->
                         let uu____74582 =
                           let uu____74584 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____74584 t  in
                         fail1 "trefl: not an equality (%s)" uu____74582))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____74373
  
let (dup : unit -> unit tac) =
  fun uu____74601  ->
    let uu____74604 = cur_goal ()  in
    bind uu____74604
      (fun g  ->
         let uu____74610 =
           let uu____74617 = FStar_Tactics_Types.goal_env g  in
           let uu____74618 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____74617 uu____74618  in
         bind uu____74610
           (fun uu____74628  ->
              match uu____74628 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___2129_74638 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___2129_74638.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___2129_74638.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___2129_74638.FStar_Tactics_Types.is_guard);
                      FStar_Tactics_Types.label =
                        (uu___2129_74638.FStar_Tactics_Types.label)
                    }  in
                  bind __dismiss
                    (fun uu____74641  ->
                       let uu____74642 =
                         let uu____74645 = FStar_Tactics_Types.goal_env g  in
                         let uu____74646 =
                           let uu____74647 =
                             let uu____74648 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____74649 =
                               FStar_Tactics_Types.goal_type g  in
                             FStar_TypeChecker_TcTerm.universe_of uu____74648
                               uu____74649
                              in
                           let uu____74650 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____74651 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____74647 uu____74650 u
                             uu____74651
                            in
                         add_irrelevant_goal "dup equation" uu____74645
                           uu____74646 g.FStar_Tactics_Types.opts
                           g.FStar_Tactics_Types.label
                          in
                       bind uu____74642
                         (fun uu____74655  ->
                            let uu____74656 = add_goals [g']  in
                            bind uu____74656 (fun uu____74660  -> ret ())))))
  
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
              let uu____74786 = f x y  in
              if uu____74786 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____74809 -> (acc, l11, l21)  in
        let uu____74824 = aux [] l1 l2  in
        match uu____74824 with | (pr,t1,t2) -> ((FStar_List.rev pr), t1, t2)
  
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
      let uu____74930 = get_phi g1  in
      match uu____74930 with
      | FStar_Pervasives_Native.None  -> fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____74937 = get_phi g2  in
          (match uu____74937 with
           | FStar_Pervasives_Native.None  -> fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let uu____74950 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2)
                  in
               (match uu____74950 with
                | (gamma,r1,r2) ->
                    let t1 =
                      let uu____74981 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1)
                         in
                      close_forall_no_univs1 uu____74981 phi1  in
                    let t2 =
                      let uu____74991 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2)
                         in
                      close_forall_no_univs1 uu____74991 phi2  in
                    let uu____75000 =
                      set_solution g1 FStar_Syntax_Util.exp_unit  in
                    bind uu____75000
                      (fun uu____75005  ->
                         let uu____75006 =
                           set_solution g2 FStar_Syntax_Util.exp_unit  in
                         bind uu____75006
                           (fun uu____75013  ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2  in
                              let nenv =
                                let uu___2180_75018 =
                                  FStar_Tactics_Types.goal_env g1  in
                                let uu____75019 =
                                  FStar_Util.smap_create
                                    (Prims.parse_int "100")
                                   in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___2180_75018.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___2180_75018.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___2180_75018.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___2180_75018.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____75019;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___2180_75018.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___2180_75018.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___2180_75018.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___2180_75018.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___2180_75018.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___2180_75018.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___2180_75018.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___2180_75018.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___2180_75018.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___2180_75018.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___2180_75018.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___2180_75018.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___2180_75018.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___2180_75018.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___2180_75018.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___2180_75018.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___2180_75018.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___2180_75018.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___2180_75018.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___2180_75018.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___2180_75018.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___2180_75018.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___2180_75018.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___2180_75018.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___2180_75018.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___2180_75018.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___2180_75018.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___2180_75018.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___2180_75018.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___2180_75018.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___2180_75018.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___2180_75018.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___2180_75018.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___2180_75018.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___2180_75018.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___2180_75018.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___2180_75018.FStar_TypeChecker_Env.nbe)
                                }  in
                              let uu____75023 =
                                mk_irrelevant_goal "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                  g1.FStar_Tactics_Types.label
                                 in
                              bind uu____75023
                                (fun goal  ->
                                   mlog
                                     (fun uu____75033  ->
                                        let uu____75034 =
                                          goal_to_string_verbose g1  in
                                        let uu____75036 =
                                          goal_to_string_verbose g2  in
                                        let uu____75038 =
                                          goal_to_string_verbose goal  in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____75034 uu____75036 uu____75038)
                                     (fun uu____75042  -> ret goal))))))
  
let (join : unit -> unit tac) =
  fun uu____75050  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____75066 =
               set
                 (let uu___2195_75071 = ps  in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___2195_75071.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.main_goal =
                      (uu___2195_75071.FStar_Tactics_Types.main_goal);
                    FStar_Tactics_Types.all_implicits =
                      (uu___2195_75071.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___2195_75071.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___2195_75071.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___2195_75071.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___2195_75071.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___2195_75071.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___2195_75071.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___2195_75071.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___2195_75071.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___2195_75071.FStar_Tactics_Types.local_state)
                  })
                in
             bind uu____75066
               (fun uu____75074  ->
                  let uu____75075 = join_goals g1 g2  in
                  bind uu____75075 (fun g12  -> add_goals [g12]))
         | uu____75080 -> fail "join: less than 2 goals")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) tac)
  =
  fun t  ->
    let uu____75102 =
      let uu____75109 = cur_goal ()  in
      bind uu____75109
        (fun g  ->
           let uu____75119 =
             let uu____75128 = FStar_Tactics_Types.goal_env g  in
             __tc uu____75128 t  in
           bind uu____75119
             (fun uu____75156  ->
                match uu____75156 with
                | (t1,typ,guard) ->
                    let uu____75172 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____75172 with
                     | (hd1,args) ->
                         let uu____75221 =
                           let uu____75236 =
                             let uu____75237 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____75237.FStar_Syntax_Syntax.n  in
                           (uu____75236, args)  in
                         (match uu____75221 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____75258)::(q,uu____75260)::[]) when
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
                                let uu____75314 =
                                  let uu____75315 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____75315
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____75314
                                 in
                              let g2 =
                                let uu____75317 =
                                  let uu____75318 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____75318
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____75317
                                 in
                              bind __dismiss
                                (fun uu____75325  ->
                                   let uu____75326 = add_goals [g1; g2]  in
                                   bind uu____75326
                                     (fun uu____75335  ->
                                        let uu____75336 =
                                          let uu____75341 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____75342 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____75341, uu____75342)  in
                                        ret uu____75336))
                          | uu____75347 ->
                              let uu____75362 =
                                let uu____75364 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____75364 typ  in
                              fail1 "Not a disjunction: %s" uu____75362))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____75102
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____75399 =
      let uu____75402 = cur_goal ()  in
      bind uu____75402
        (fun g  ->
           FStar_Options.push ();
           (let uu____75415 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____75415);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___2232_75422 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___2232_75422.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___2232_75422.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___2232_75422.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___2232_75422.FStar_Tactics_Types.label)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____75399
  
let (top_env : unit -> env tac) =
  fun uu____75439  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____75454  ->
    let uu____75458 = cur_goal ()  in
    bind uu____75458
      (fun g  ->
         let uu____75465 =
           (FStar_Options.lax ()) ||
             (let uu____75468 = FStar_Tactics_Types.goal_env g  in
              uu____75468.FStar_TypeChecker_Env.lax)
            in
         ret uu____75465)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____75485 =
        mlog
          (fun uu____75490  ->
             let uu____75491 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____75491)
          (fun uu____75496  ->
             let uu____75497 = cur_goal ()  in
             bind uu____75497
               (fun goal  ->
                  let env =
                    let uu____75505 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____75505 ty  in
                  let uu____75506 = __tc_ghost env tm  in
                  bind uu____75506
                    (fun uu____75525  ->
                       match uu____75525 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____75539  ->
                                let uu____75540 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____75540)
                             (fun uu____75544  ->
                                mlog
                                  (fun uu____75547  ->
                                     let uu____75548 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____75548)
                                  (fun uu____75553  ->
                                     let uu____75554 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____75554
                                       (fun uu____75559  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____75485
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____75584 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____75590 =
              let uu____75597 =
                let uu____75598 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____75598
                 in
              new_uvar "uvar_env.2" env uu____75597  in
            bind uu____75590
              (fun uu____75615  ->
                 match uu____75615 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____75584
        (fun typ  ->
           let uu____75627 = new_uvar "uvar_env" env typ  in
           bind uu____75627
             (fun uu____75642  ->
                match uu____75642 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____75661 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____75680 -> g.FStar_Tactics_Types.opts
             | uu____75683 -> FStar_Options.peek ()  in
           let uu____75686 = FStar_Syntax_Util.head_and_args t  in
           match uu____75686 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____75706);
                FStar_Syntax_Syntax.pos = uu____75707;
                FStar_Syntax_Syntax.vars = uu____75708;_},uu____75709)
               ->
               let env1 =
                 let uu___2286_75751 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___2286_75751.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___2286_75751.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___2286_75751.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___2286_75751.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___2286_75751.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___2286_75751.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___2286_75751.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___2286_75751.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___2286_75751.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___2286_75751.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___2286_75751.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___2286_75751.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___2286_75751.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___2286_75751.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___2286_75751.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___2286_75751.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___2286_75751.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___2286_75751.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___2286_75751.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___2286_75751.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___2286_75751.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___2286_75751.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___2286_75751.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___2286_75751.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___2286_75751.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___2286_75751.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___2286_75751.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___2286_75751.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___2286_75751.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___2286_75751.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___2286_75751.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___2286_75751.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___2286_75751.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___2286_75751.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___2286_75751.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___2286_75751.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___2286_75751.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___2286_75751.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___2286_75751.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___2286_75751.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___2286_75751.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___2286_75751.FStar_TypeChecker_Env.nbe)
                 }  in
               let g =
                 FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false ""  in
               let uu____75755 =
                 let uu____75758 = bnorm_goal g  in [uu____75758]  in
               add_goals uu____75755
           | uu____75759 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____75661
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____75821 = if b then t2 else ret false  in
             bind uu____75821 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____75847 = trytac comp  in
      bind uu____75847
        (fun uu___613_75859  ->
           match uu___613_75859 with
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
        let uu____75901 =
          bind get
            (fun ps  ->
               let uu____75909 = __tc e t1  in
               bind uu____75909
                 (fun uu____75930  ->
                    match uu____75930 with
                    | (t11,ty1,g1) ->
                        let uu____75943 = __tc e t2  in
                        bind uu____75943
                          (fun uu____75964  ->
                             match uu____75964 with
                             | (t21,ty2,g2) ->
                                 let uu____75977 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____75977
                                   (fun uu____75984  ->
                                      let uu____75985 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____75985
                                        (fun uu____75993  ->
                                           let uu____75994 =
                                             do_unify e ty1 ty2  in
                                           let uu____75998 =
                                             do_unify e t11 t21  in
                                           tac_and uu____75994 uu____75998)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____75901
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____76046  ->
             let uu____76047 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____76047
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
        (fun uu____76081  ->
           let uu____76082 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____76082)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____76093 =
      mlog
        (fun uu____76098  ->
           let uu____76099 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____76099)
        (fun uu____76104  ->
           let uu____76105 = cur_goal ()  in
           bind uu____76105
             (fun g  ->
                let uu____76111 =
                  let uu____76120 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____76120 ty  in
                bind uu____76111
                  (fun uu____76132  ->
                     match uu____76132 with
                     | (ty1,uu____76142,guard) ->
                         let uu____76144 =
                           let uu____76147 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____76147 guard  in
                         bind uu____76144
                           (fun uu____76151  ->
                              let uu____76152 =
                                let uu____76156 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____76157 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____76156 uu____76157 ty1  in
                              bind uu____76152
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____76166 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____76166
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops]  in
                                      let ng =
                                        let uu____76173 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____76174 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____76173
                                          uu____76174
                                         in
                                      let nty =
                                        let uu____76176 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____76176 ty1  in
                                      let uu____76177 =
                                        let uu____76181 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____76181 ng nty  in
                                      bind uu____76177
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____76190 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____76190
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____76093
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) Prims.list tac)
  =
  fun s_tm  ->
    let uu____76264 =
      let uu____76273 = cur_goal ()  in
      bind uu____76273
        (fun g  ->
           let uu____76285 =
             let uu____76294 = FStar_Tactics_Types.goal_env g  in
             __tc uu____76294 s_tm  in
           bind uu____76285
             (fun uu____76312  ->
                match uu____76312 with
                | (s_tm1,s_ty,guard) ->
                    let uu____76330 =
                      let uu____76333 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____76333 guard  in
                    bind uu____76330
                      (fun uu____76346  ->
                         let uu____76347 =
                           FStar_Syntax_Util.head_and_args' s_ty  in
                         match uu____76347 with
                         | (h,args) ->
                             let uu____76392 =
                               let uu____76399 =
                                 let uu____76400 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____76400.FStar_Syntax_Syntax.n  in
                               match uu____76399 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____76415;
                                      FStar_Syntax_Syntax.vars = uu____76416;_},us)
                                   -> ret (fv, us)
                               | uu____76426 -> fail "type is not an fv"  in
                             bind uu____76392
                               (fun uu____76447  ->
                                  match uu____76447 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____76463 =
                                        let uu____76466 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____76466 t_lid
                                         in
                                      (match uu____76463 with
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
                                                  (fun uu____76517  ->
                                                     let uu____76518 =
                                                       FStar_Syntax_Subst.open_term
                                                         t_ps t_ty
                                                        in
                                                     match uu____76518 with
                                                     | (t_ps1,t_ty1) ->
                                                         let uu____76533 =
                                                           mapM
                                                             (fun c_lid  ->
                                                                let uu____76561
                                                                  =
                                                                  let uu____76564
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                  FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____76564
                                                                    c_lid
                                                                   in
                                                                match uu____76561
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
                                                                    uu____76638
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
                                                                    let uu____76643
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____76643
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____76666
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____76666
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____76709
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs
                                                                     in
                                                                    (match uu____76709
                                                                    with
                                                                    | 
                                                                    (d_ps,bs1)
                                                                    ->
                                                                    let uu____76782
                                                                    =
                                                                    let uu____76784
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp  in
                                                                    Prims.op_Negation
                                                                    uu____76784
                                                                     in
                                                                    failwhen
                                                                    uu____76782
                                                                    "not total?"
                                                                    (fun
                                                                    uu____76803
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
                                                                    uu___614_76820
                                                                    =
                                                                    match uu___614_76820
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____76824)
                                                                    -> true
                                                                    | 
                                                                    uu____76827
                                                                    -> false
                                                                     in
                                                                    let uu____76831
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____76831
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
                                                                    uu____76965
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
                                                                    uu____77027
                                                                     ->
                                                                    match uu____77027
                                                                    with
                                                                    | 
                                                                    ((bv,uu____77047),
                                                                    (t,uu____77049))
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
                                                                    uu____77119
                                                                     ->
                                                                    match uu____77119
                                                                    with
                                                                    | 
                                                                    ((bv,uu____77146),
                                                                    (t,uu____77148))
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
                                                                    uu____77207
                                                                     ->
                                                                    match uu____77207
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
                                                                    let uu____77262
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___2450_77279
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___2450_77279.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___2450_77279.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___2450_77279.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___2450_77279.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___2450_77279.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___2450_77279.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___2450_77279.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___2450_77279.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___2450_77279.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___2450_77279.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___2450_77279.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___2450_77279.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___2450_77279.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___2450_77279.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___2450_77279.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___2450_77279.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___2450_77279.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___2450_77279.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___2450_77279.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___2450_77279.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___2450_77279.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___2450_77279.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___2450_77279.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___2450_77279.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___2450_77279.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___2450_77279.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___2450_77279.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___2450_77279.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___2450_77279.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___2450_77279.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___2450_77279.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___2450_77279.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___2450_77279.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___2450_77279.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___2450_77279.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___2450_77279.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___2450_77279.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___2450_77279.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___2450_77279.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___2450_77279.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___2450_77279.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___2450_77279.FStar_TypeChecker_Env.nbe)
                                                                    }) s_ty
                                                                    pat  in
                                                                    match uu____77262
                                                                    with
                                                                    | 
                                                                    (uu____77293,uu____77294,uu____77295,pat_t,uu____77297,_guard_pat)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____77304
                                                                    =
                                                                    let uu____77305
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____77305
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____77304
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____77310
                                                                    =
                                                                    let uu____77319
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____77319]
                                                                     in
                                                                    let uu____77338
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____77310
                                                                    uu____77338
                                                                     in
                                                                    let nty =
                                                                    let uu____77344
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____77344
                                                                     in
                                                                    let uu____77347
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____77347
                                                                    (fun
                                                                    uu____77377
                                                                     ->
                                                                    match uu____77377
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
                                                                    let uu____77404
                                                                    =
                                                                    let uu____77415
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____77415]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____77404
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____77451
                                                                    =
                                                                    let uu____77462
                                                                    =
                                                                    let uu____77467
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2)  in
                                                                    (fv1,
                                                                    uu____77467)
                                                                     in
                                                                    (g', br,
                                                                    uu____77462)
                                                                     in
                                                                    ret
                                                                    uu____77451))))))
                                                                    | 
                                                                    uu____77488
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                             c_lids
                                                            in
                                                         bind uu____76533
                                                           (fun goal_brs  ->
                                                              let uu____77538
                                                                =
                                                                FStar_List.unzip3
                                                                  goal_brs
                                                                 in
                                                              match uu____77538
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
                                                                  let uu____77611
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                  bind
                                                                    uu____77611
                                                                    (
                                                                    fun
                                                                    uu____77622
                                                                     ->
                                                                    let uu____77623
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____77623
                                                                    (fun
                                                                    uu____77633
                                                                     ->
                                                                    ret infos))))
                                            | uu____77640 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____76264
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____77689::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____77719 = init xs  in x :: uu____77719
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____77732 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      let t3 = FStar_Syntax_Util.unlazy_emb t2  in
      match t3.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____77741) -> inspect t4
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____77807 = last args  in
          (match uu____77807 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____77837 =
                 let uu____77838 =
                   let uu____77843 =
                     let uu____77844 =
                       let uu____77849 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____77849  in
                     uu____77844 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____77843, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____77838  in
               FStar_All.pipe_left ret uu____77837)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____77860,uu____77861) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
          let uu____77914 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____77914 with
           | (bs1,t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____77956 =
                      let uu____77957 =
                        let uu____77962 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____77962)  in
                      FStar_Reflection_Data.Tv_Abs uu____77957  in
                    FStar_All.pipe_left ret uu____77956))
      | FStar_Syntax_Syntax.Tm_type uu____77965 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____77990 ->
          let uu____78005 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____78005 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____78036 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____78036 with
           | (b',t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____78089 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____78102 =
            let uu____78103 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____78103  in
          FStar_All.pipe_left ret uu____78102
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____78124 =
            let uu____78125 =
              let uu____78130 =
                let uu____78131 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____78131  in
              (uu____78130, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____78125  in
          FStar_All.pipe_left ret uu____78124
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____78171 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____78176 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____78176 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____78229 ->
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
             | FStar_Util.Inr uu____78271 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____78275 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____78275 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____78295 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____78301 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____78356 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____78356
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____78377 =
                  let uu____78384 =
                    FStar_List.map
                      (fun uu____78397  ->
                         match uu____78397 with
                         | (p1,uu____78406) -> inspect_pat p1) ps
                     in
                  (fv, uu____78384)  in
                FStar_Reflection_Data.Pat_Cons uu____78377
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
              (fun uu___615_78502  ->
                 match uu___615_78502 with
                 | (pat,uu____78524,t5) ->
                     let uu____78542 = inspect_pat pat  in (uu____78542, t5))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____78551 ->
          ((let uu____78553 =
              let uu____78559 =
                let uu____78561 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____78563 = FStar_Syntax_Print.term_to_string t3  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____78561 uu____78563
                 in
              (FStar_Errors.Warning_CantInspect, uu____78559)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____78553);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____77732
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____78581 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____78581
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____78585 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____78585
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____78589 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____78589
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____78596 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____78596
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____78621 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____78621
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____78638 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____78638
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____78657 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____78657
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____78661 =
          let uu____78662 =
            let uu____78669 =
              let uu____78670 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____78670  in
            FStar_Syntax_Syntax.mk uu____78669  in
          uu____78662 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____78661
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____78675 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____78675
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____78686 =
          let uu____78687 =
            let uu____78694 =
              let uu____78695 =
                let uu____78709 =
                  let uu____78712 =
                    let uu____78713 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____78713]  in
                  FStar_Syntax_Subst.close uu____78712 t2  in
                ((false, [lb]), uu____78709)  in
              FStar_Syntax_Syntax.Tm_let uu____78695  in
            FStar_Syntax_Syntax.mk uu____78694  in
          uu____78687 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____78686
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____78755 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____78755 with
         | (lbs,body) ->
             let uu____78770 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____78770)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____78807 =
                let uu____78808 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____78808  in
              FStar_All.pipe_left wrap uu____78807
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____78815 =
                let uu____78816 =
                  let uu____78830 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____78848 = pack_pat p1  in
                         (uu____78848, false)) ps
                     in
                  (fv, uu____78830)  in
                FStar_Syntax_Syntax.Pat_cons uu____78816  in
              FStar_All.pipe_left wrap uu____78815
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
            (fun uu___616_78897  ->
               match uu___616_78897 with
               | (pat,t1) ->
                   let uu____78914 = pack_pat pat  in
                   (uu____78914, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____78962 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____78962
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____78990 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____78990
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____79036 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____79036
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____79075 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____79075
  
let (lget :
  FStar_Reflection_Data.typ -> Prims.string -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun k  ->
      let uu____79095 =
        bind get
          (fun ps  ->
             let uu____79101 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____79101 with
             | FStar_Pervasives_Native.None  -> fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
      FStar_All.pipe_left (wrap_err "lget") uu____79095
  
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit tac)
  =
  fun _ty  ->
    fun k  ->
      fun t  ->
        let uu____79135 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___2748_79142 = ps  in
                 let uu____79143 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t
                    in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___2748_79142.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___2748_79142.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___2748_79142.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___2748_79142.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___2748_79142.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___2748_79142.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___2748_79142.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___2748_79142.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___2748_79142.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___2748_79142.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___2748_79142.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___2748_79142.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____79143
                 }  in
               set ps1)
           in
        FStar_All.pipe_left (wrap_err "lset") uu____79135
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal * FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun typ  ->
      let uu____79170 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____79170 with
      | (u,ctx_uvars,g_u) ->
          let uu____79203 = FStar_List.hd ctx_uvars  in
          (match uu____79203 with
           | (ctx_uvar,uu____79217) ->
               let g =
                 let uu____79219 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____79219 false
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
        let uu____79242 = goal_of_goal_ty env typ  in
        match uu____79242 with
        | (g,g_u) ->
            let ps =
              let uu____79254 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "TacVerbose")
                 in
              let uu____79257 = FStar_Util.psmap_empty ()  in
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
                FStar_Tactics_Types.tac_verb_dbg = uu____79254;
                FStar_Tactics_Types.local_state = uu____79257
              }  in
            let uu____79267 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____79267)
  