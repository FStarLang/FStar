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
    let uu____68809 =
      let uu____68810 = FStar_Tactics_Types.goal_env g  in
      let uu____68811 = FStar_Tactics_Types.goal_type g  in
      bnorm uu____68810 uu____68811  in
    FStar_Tactics_Types.goal_with_type g uu____68809
  
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
      let uu____68925 = FStar_Options.tactics_failhard ()  in
      if uu____68925
      then run t p
      else
        (try (fun uu___640_68935  -> match () with | () -> run t p) ()
         with
         | FStar_Errors.Err (uu____68944,msg) ->
             FStar_Tactics_Result.Failed
               ((FStar_Tactics_Types.TacticFailure msg), p)
         | FStar_Errors.Error (uu____68948,msg,uu____68950) ->
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
           let uu____69030 = run t1 p  in
           match uu____69030 with
           | FStar_Tactics_Result.Success (a,q) ->
               let uu____69037 = t2 a  in run uu____69037 q
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
    let uu____69060 =
      FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head  in
    match uu____69060 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (check_goal_solved :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun goal  -> get_uvar_solved goal.FStar_Tactics_Types.goal_ctx_uvar 
let (goal_to_string_verbose : FStar_Tactics_Types.goal -> Prims.string) =
  fun g  ->
    let uu____69082 =
      FStar_Syntax_Print.ctx_uvar_to_string
        g.FStar_Tactics_Types.goal_ctx_uvar
       in
    let uu____69084 =
      let uu____69086 = check_goal_solved g  in
      match uu____69086 with
      | FStar_Pervasives_Native.None  -> ""
      | FStar_Pervasives_Native.Some t ->
          let uu____69092 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "\tGOAL ALREADY SOLVED!: %s" uu____69092
       in
    FStar_Util.format2 "%s%s\n" uu____69082 uu____69084
  
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
            let uu____69139 = FStar_Options.print_implicits ()  in
            if uu____69139
            then
              let uu____69143 = FStar_Tactics_Types.goal_env g  in
              let uu____69144 = FStar_Tactics_Types.goal_witness g  in
              tts uu____69143 uu____69144
            else
              (let uu____69147 =
                 get_uvar_solved g.FStar_Tactics_Types.goal_ctx_uvar  in
               match uu____69147 with
               | FStar_Pervasives_Native.None  -> "_"
               | FStar_Pervasives_Native.Some t ->
                   let uu____69153 = FStar_Tactics_Types.goal_env g  in
                   let uu____69154 = FStar_Tactics_Types.goal_witness g  in
                   tts uu____69153 uu____69154)
             in
          let num =
            match maybe_num with
            | FStar_Pervasives_Native.None  -> ""
            | FStar_Pervasives_Native.Some (i,n1) ->
                let uu____69177 = FStar_Util.string_of_int i  in
                let uu____69179 = FStar_Util.string_of_int n1  in
                FStar_Util.format2 " %s/%s" uu____69177 uu____69179
             in
          let maybe_label =
            match g.FStar_Tactics_Types.label with
            | "" -> ""
            | l -> Prims.op_Hat " (" (Prims.op_Hat l ")")  in
          let actual_goal =
            if ps.FStar_Tactics_Types.tac_verb_dbg
            then goal_to_string_verbose g
            else
              (let uu____69197 =
                 FStar_Syntax_Print.binders_to_string ", "
                   (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
                  in
               let uu____69200 =
                 let uu____69202 = FStar_Tactics_Types.goal_env g  in
                 tts uu____69202
                   (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                  in
               FStar_Util.format3 "%s |- %s : %s\n" uu____69197 w uu____69200)
             in
          FStar_Util.format4 "%s%s%s:\n%s\n" kind num maybe_label actual_goal
  
let (tacprint : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      let uu____69229 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____69229
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____69254 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____69254
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____69286 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____69286
  
let (comp_to_typ : FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____69296) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____69306) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (get_phi :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun g  ->
    let uu____69326 =
      let uu____69327 = FStar_Tactics_Types.goal_env g  in
      let uu____69328 = FStar_Tactics_Types.goal_type g  in
      FStar_TypeChecker_Normalize.unfold_whnf uu____69327 uu____69328  in
    FStar_Syntax_Util.un_squash uu____69326
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  -> let uu____69337 = get_phi g  in FStar_Option.isSome uu____69337 
let (print : Prims.string -> unit tac) = fun msg  -> tacprint msg; ret () 
let (debugging : unit -> Prims.bool tac) =
  fun uu____69361  ->
    bind get
      (fun ps  ->
         let uu____69369 =
           FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
             (FStar_Options.Other "Tac")
            in
         ret uu____69369)
  
let (ps_to_string :
  (Prims.string * FStar_Tactics_Types.proofstate) -> Prims.string) =
  fun uu____69384  ->
    match uu____69384 with
    | (msg,ps) ->
        let p_imp imp =
          FStar_Syntax_Print.uvar_to_string
            (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
           in
        let n_active = FStar_List.length ps.FStar_Tactics_Types.goals  in
        let n_smt = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
        let n1 = n_active + n_smt  in
        let uu____69416 =
          let uu____69420 =
            let uu____69424 =
              let uu____69426 =
                FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
              FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____69426
                msg
               in
            let uu____69429 =
              let uu____69433 =
                if
                  ps.FStar_Tactics_Types.entry_range <>
                    FStar_Range.dummyRange
                then
                  let uu____69437 =
                    FStar_Range.string_of_def_range
                      ps.FStar_Tactics_Types.entry_range
                     in
                  FStar_Util.format1 "Location: %s\n" uu____69437
                else ""  in
              let uu____69443 =
                let uu____69447 =
                  let uu____69449 =
                    FStar_TypeChecker_Env.debug
                      ps.FStar_Tactics_Types.main_context
                      (FStar_Options.Other "Imp")
                     in
                  if uu____69449
                  then
                    let uu____69454 =
                      FStar_Common.string_of_list p_imp
                        ps.FStar_Tactics_Types.all_implicits
                       in
                    FStar_Util.format1 "Imps: %s\n" uu____69454
                  else ""  in
                [uu____69447]  in
              uu____69433 :: uu____69443  in
            uu____69424 :: uu____69429  in
          let uu____69464 =
            let uu____69468 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "Goal"
                       (FStar_Pervasives_Native.Some
                          (((Prims.parse_int "1") + i), n1)) ps g)
                ps.FStar_Tactics_Types.goals
               in
            let uu____69488 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "SMT Goal"
                       (FStar_Pervasives_Native.Some
                          ((((Prims.parse_int "1") + n_active) + i), n1)) ps
                       g) ps.FStar_Tactics_Types.smt_goals
               in
            FStar_List.append uu____69468 uu____69488  in
          FStar_List.append uu____69420 uu____69464  in
        FStar_String.concat "" uu____69416
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      let uu____69522 =
        let uu____69523 = FStar_Tactics_Types.goal_env g  in
        FStar_TypeChecker_Env.all_binders uu____69523  in
      let uu____69524 =
        let uu____69529 =
          let uu____69530 = FStar_Tactics_Types.goal_env g  in
          FStar_TypeChecker_Env.dsenv uu____69530  in
        FStar_Syntax_Print.binders_to_json uu____69529  in
      FStar_All.pipe_right uu____69522 uu____69524  in
    let uu____69531 =
      let uu____69539 =
        let uu____69547 =
          let uu____69553 =
            let uu____69554 =
              let uu____69562 =
                let uu____69568 =
                  let uu____69569 =
                    let uu____69571 = FStar_Tactics_Types.goal_env g  in
                    let uu____69572 = FStar_Tactics_Types.goal_witness g  in
                    tts uu____69571 uu____69572  in
                  FStar_Util.JsonStr uu____69569  in
                ("witness", uu____69568)  in
              let uu____69575 =
                let uu____69583 =
                  let uu____69589 =
                    let uu____69590 =
                      let uu____69592 = FStar_Tactics_Types.goal_env g  in
                      let uu____69593 = FStar_Tactics_Types.goal_type g  in
                      tts uu____69592 uu____69593  in
                    FStar_Util.JsonStr uu____69590  in
                  ("type", uu____69589)  in
                [uu____69583;
                ("label", (FStar_Util.JsonStr (g.FStar_Tactics_Types.label)))]
                 in
              uu____69562 :: uu____69575  in
            FStar_Util.JsonAssoc uu____69554  in
          ("goal", uu____69553)  in
        [uu____69547]  in
      ("hyps", g_binders) :: uu____69539  in
    FStar_Util.JsonAssoc uu____69531
  
let (ps_to_json :
  (Prims.string * FStar_Tactics_Types.proofstate) -> FStar_Util.json) =
  fun uu____69647  ->
    match uu____69647 with
    | (msg,ps) ->
        let uu____69657 =
          let uu____69665 =
            let uu____69673 =
              let uu____69681 =
                let uu____69689 =
                  let uu____69695 =
                    let uu____69696 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____69696  in
                  ("goals", uu____69695)  in
                let uu____69701 =
                  let uu____69709 =
                    let uu____69715 =
                      let uu____69716 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____69716  in
                    ("smt-goals", uu____69715)  in
                  [uu____69709]  in
                uu____69689 :: uu____69701  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____69681
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____69673  in
          let uu____69750 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____69766 =
                let uu____69772 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____69772)  in
              [uu____69766]
            else []  in
          FStar_List.append uu____69665 uu____69750  in
        FStar_Util.JsonAssoc uu____69657
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____69812  ->
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
         (let uu____69843 = FStar_Tactics_Types.subst_proof_state subst1 ps
             in
          dump_proofstate uu____69843 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let traise : 'a . Prims.exn -> 'a tac =
  fun e  -> mk_tac (fun ps  -> FStar_Tactics_Result.Failed (e, ps)) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____69916 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____69916
          then dump_proofstate ps (Prims.op_Hat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed
           ((FStar_Tactics_Types.TacticFailure msg), ps))
  
let fail1 : 'Auu____69930 . Prims.string -> Prims.string -> 'Auu____69930 tac
  =
  fun msg  ->
    fun x  -> let uu____69947 = FStar_Util.format1 msg x  in fail uu____69947
  
let fail2 :
  'Auu____69958 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____69958 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        let uu____69982 = FStar_Util.format2 msg x y  in fail uu____69982
  
let fail3 :
  'Auu____69995 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____69995 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____70026 = FStar_Util.format3 msg x y z  in fail uu____70026
  
let fail4 :
  'Auu____70041 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____70041 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____70079 = FStar_Util.format4 msg x y z w  in
            fail uu____70079
  
let catch : 'a . 'a tac -> (Prims.exn,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____70114 = run t ps  in
         match uu____70114 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___802_70138 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___802_70138.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___802_70138.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___802_70138.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___802_70138.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___802_70138.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___802_70138.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___802_70138.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___802_70138.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___802_70138.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___802_70138.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___802_70138.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (uu___802_70138.FStar_Tactics_Types.local_state)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let recover : 'a . 'a tac -> (Prims.exn,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let uu____70177 = run t ps  in
         match uu____70177 with
         | FStar_Tactics_Result.Success (a,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inr a), q)
         | FStar_Tactics_Result.Failed (m,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inl m), q))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____70225 = catch t  in
    bind uu____70225
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____70252 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try
           (fun uu___828_70284  ->
              match () with
              | () -> let uu____70289 = trytac t  in run uu____70289 ps) ()
         with
         | FStar_Errors.Err (uu____70305,msg) ->
             (log ps
                (fun uu____70311  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____70317,msg,uu____70319) ->
             (log ps
                (fun uu____70324  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____70361 = run t ps  in
           match uu____70361 with
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
  fun p  -> mk_tac (fun uu____70385  -> FStar_Tactics_Result.Success ((), p)) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___863_70400 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___863_70400.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___863_70400.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___863_70400.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___863_70400.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___863_70400.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___863_70400.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___863_70400.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___863_70400.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___863_70400.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___863_70400.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___863_70400.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___863_70400.FStar_Tactics_Types.local_state)
            }))
  
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____70424 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____70424
         then
           let uu____70428 = FStar_Syntax_Print.term_to_string t1  in
           let uu____70430 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____70428
             uu____70430
         else ());
        (try
           (fun uu___871_70441  ->
              match () with
              | () ->
                  let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
                  ((let uu____70449 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____70449
                    then
                      let uu____70453 =
                        FStar_Common.string_of_option
                          (FStar_TypeChecker_Rel.guard_to_string env) res
                         in
                      let uu____70455 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____70457 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.print3
                        "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____70453
                        uu____70455 uu____70457
                    else ());
                   (match res with
                    | FStar_Pervasives_Native.None  -> ret false
                    | FStar_Pervasives_Native.Some g ->
                        let uu____70468 =
                          add_implicits g.FStar_TypeChecker_Env.implicits  in
                        bind uu____70468 (fun uu____70473  -> ret true)))) ()
         with
         | FStar_Errors.Err (uu____70483,msg) ->
             mlog
               (fun uu____70489  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____70492  -> ret false)
         | FStar_Errors.Error (uu____70495,msg,r) ->
             mlog
               (fun uu____70503  ->
                  let uu____70504 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____70504) (fun uu____70508  -> ret false))
  
let (compress_implicits : unit tac) =
  bind get
    (fun ps  ->
       let imps = ps.FStar_Tactics_Types.all_implicits  in
       let g =
         let uu___897_70522 = FStar_TypeChecker_Env.trivial_guard  in
         {
           FStar_TypeChecker_Env.guard_f =
             (uu___897_70522.FStar_TypeChecker_Env.guard_f);
           FStar_TypeChecker_Env.deferred =
             (uu___897_70522.FStar_TypeChecker_Env.deferred);
           FStar_TypeChecker_Env.univ_ineqs =
             (uu___897_70522.FStar_TypeChecker_Env.univ_ineqs);
           FStar_TypeChecker_Env.implicits = imps
         }  in
       let g1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g
          in
       let ps' =
         let uu___901_70525 = ps  in
         {
           FStar_Tactics_Types.main_context =
             (uu___901_70525.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___901_70525.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (g1.FStar_TypeChecker_Env.implicits);
           FStar_Tactics_Types.goals =
             (uu___901_70525.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___901_70525.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___901_70525.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___901_70525.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___901_70525.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___901_70525.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___901_70525.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___901_70525.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___901_70525.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___901_70525.FStar_Tactics_Types.local_state)
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
          (fun uu____70552  ->
             (let uu____70554 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____70554
              then
                (FStar_Options.push ();
                 (let uu____70559 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____70563 = __do_unify env t1 t2  in
              bind uu____70563
                (fun r  ->
                   (let uu____70574 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____70574 then FStar_Options.pop () else ());
                   ret r)))
  
let (remove_solved_goals : unit tac) =
  bind get
    (fun ps  ->
       let ps' =
         let uu___916_70588 = ps  in
         let uu____70589 =
           FStar_List.filter
             (fun g  ->
                let uu____70595 = check_goal_solved g  in
                FStar_Option.isNone uu____70595) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___916_70588.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___916_70588.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___916_70588.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____70589;
           FStar_Tactics_Types.smt_goals =
             (uu___916_70588.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___916_70588.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___916_70588.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___916_70588.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___916_70588.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___916_70588.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___916_70588.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___916_70588.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___916_70588.FStar_Tactics_Types.local_state)
         }  in
       set ps')
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____70613 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____70613 with
      | FStar_Pervasives_Native.Some uu____70618 ->
          let uu____70619 =
            let uu____70621 = goal_to_string_verbose goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____70621  in
          fail uu____70619
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____70642 = FStar_Tactics_Types.goal_env goal  in
      let uu____70643 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____70642 solution uu____70643
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____70650 =
         let uu___929_70651 = p  in
         let uu____70652 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___929_70651.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___929_70651.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___929_70651.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____70652;
           FStar_Tactics_Types.smt_goals =
             (uu___929_70651.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___929_70651.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___929_70651.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___929_70651.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___929_70651.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___929_70651.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___929_70651.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___929_70651.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___929_70651.FStar_Tactics_Types.local_state)
         }  in
       set uu____70650)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      mlog
        (fun uu____70674  ->
           let uu____70675 =
             let uu____70677 = FStar_Tactics_Types.goal_witness goal  in
             FStar_Syntax_Print.term_to_string uu____70677  in
           let uu____70678 = FStar_Syntax_Print.term_to_string solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____70675 uu____70678)
        (fun uu____70683  ->
           let uu____70684 = trysolve goal solution  in
           bind uu____70684
             (fun b  ->
                if b
                then bind __dismiss (fun uu____70696  -> remove_solved_goals)
                else
                  (let uu____70699 =
                     let uu____70701 =
                       let uu____70703 = FStar_Tactics_Types.goal_env goal
                          in
                       tts uu____70703 solution  in
                     let uu____70704 =
                       let uu____70706 = FStar_Tactics_Types.goal_env goal
                          in
                       let uu____70707 =
                         FStar_Tactics_Types.goal_witness goal  in
                       tts uu____70706 uu____70707  in
                     let uu____70708 =
                       let uu____70710 = FStar_Tactics_Types.goal_env goal
                          in
                       let uu____70711 = FStar_Tactics_Types.goal_type goal
                          in
                       tts uu____70710 uu____70711  in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____70701 uu____70704 uu____70708
                      in
                   fail uu____70699)))
  
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____70728 = set_solution goal solution  in
      bind uu____70728
        (fun uu____70732  ->
           bind __dismiss (fun uu____70734  -> remove_solved_goals))
  
let (set_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___945_70753 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___945_70753.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___945_70753.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___945_70753.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals = gs;
              FStar_Tactics_Types.smt_goals =
                (uu___945_70753.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___945_70753.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___945_70753.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___945_70753.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___945_70753.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___945_70753.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___945_70753.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___945_70753.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___945_70753.FStar_Tactics_Types.local_state)
            }))
  
let (set_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___949_70772 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___949_70772.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___949_70772.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___949_70772.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___949_70772.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals = gs;
              FStar_Tactics_Types.depth =
                (uu___949_70772.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___949_70772.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___949_70772.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___949_70772.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___949_70772.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___949_70772.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___949_70772.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___949_70772.FStar_Tactics_Types.local_state)
            }))
  
let (dismiss_all : unit tac) = set_goals [] 
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____70799 = FStar_Options.defensive ()  in
    if uu____70799
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____70809 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____70809)
         in
      let b2 =
        b1 &&
          (let uu____70813 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____70813)
         in
      let rec aux b3 e =
        let uu____70828 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____70828 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____70848 =
        (let uu____70852 = aux b2 env  in Prims.op_Negation uu____70852) &&
          (let uu____70855 = FStar_ST.op_Bang nwarn  in
           uu____70855 < (Prims.parse_int "5"))
         in
      (if uu____70848
       then
         ((let uu____70881 =
             let uu____70882 = FStar_Tactics_Types.goal_type g  in
             uu____70882.FStar_Syntax_Syntax.pos  in
           let uu____70885 =
             let uu____70891 =
               let uu____70893 = goal_to_string_verbose g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____70893
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____70891)  in
           FStar_Errors.log_issue uu____70881 uu____70885);
          (let uu____70897 =
             let uu____70899 = FStar_ST.op_Bang nwarn  in
             uu____70899 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____70897))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___971_70968 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___971_70968.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___971_70968.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___971_70968.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___971_70968.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___971_70968.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___971_70968.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___971_70968.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___971_70968.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___971_70968.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___971_70968.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___971_70968.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___971_70968.FStar_Tactics_Types.local_state)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___976_70989 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___976_70989.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___976_70989.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___976_70989.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___976_70989.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___976_70989.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___976_70989.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___976_70989.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___976_70989.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___976_70989.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___976_70989.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___976_70989.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___976_70989.FStar_Tactics_Types.local_state)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___981_71010 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___981_71010.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___981_71010.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___981_71010.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___981_71010.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___981_71010.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___981_71010.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___981_71010.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___981_71010.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___981_71010.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___981_71010.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___981_71010.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___981_71010.FStar_Tactics_Types.local_state)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___986_71031 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___986_71031.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___986_71031.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___986_71031.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___986_71031.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___986_71031.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___986_71031.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___986_71031.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___986_71031.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___986_71031.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___986_71031.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___986_71031.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___986_71031.FStar_Tactics_Types.local_state)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____71043  -> add_goals [g]) 
let (new_uvar :
  Prims.string ->
    env ->
      FStar_Reflection_Data.typ ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar) tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____71074 =
          FStar_TypeChecker_Env.new_implicit_var_aux reason
            typ.FStar_Syntax_Syntax.pos env typ
            FStar_Syntax_Syntax.Allow_untyped FStar_Pervasives_Native.None
           in
        match uu____71074 with
        | (u,ctx_uvar,g_u) ->
            let uu____71112 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____71112
              (fun uu____71121  ->
                 let uu____71122 =
                   let uu____71127 =
                     let uu____71128 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____71128  in
                   (u, uu____71127)  in
                 ret uu____71122)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____71149 = FStar_Syntax_Util.un_squash t1  in
    match uu____71149 with
    | FStar_Pervasives_Native.Some t' ->
        let t'1 = FStar_Syntax_Util.unascribe t'  in
        let uu____71161 =
          let uu____71162 = FStar_Syntax_Subst.compress t'1  in
          uu____71162.FStar_Syntax_Syntax.n  in
        (match uu____71161 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____71167 -> false)
    | uu____71169 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____71182 = FStar_Syntax_Util.un_squash t  in
    match uu____71182 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____71193 =
          let uu____71194 = FStar_Syntax_Subst.compress t'  in
          uu____71194.FStar_Syntax_Syntax.n  in
        (match uu____71193 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____71199 -> false)
    | uu____71201 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____71214  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____71226 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____71226 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____71233 = goal_to_string_verbose hd1  in
                    let uu____71235 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____71233 uu____71235);
                   ret hd1)))
  
let (tadmit_t : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____71248 =
      bind get
        (fun ps  ->
           let uu____71254 = cur_goal ()  in
           bind uu____71254
             (fun g  ->
                (let uu____71261 =
                   let uu____71262 = FStar_Tactics_Types.goal_type g  in
                   uu____71262.FStar_Syntax_Syntax.pos  in
                 let uu____71265 =
                   let uu____71271 =
                     let uu____71273 =
                       goal_to_string "" FStar_Pervasives_Native.None ps g
                        in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____71273
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____71271)  in
                 FStar_Errors.log_issue uu____71261 uu____71265);
                solve' g t))
       in
    FStar_All.pipe_left (wrap_err "tadmit_t") uu____71248
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____71296  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___1031_71307 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___1031_71307.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___1031_71307.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___1031_71307.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___1031_71307.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___1031_71307.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___1031_71307.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___1031_71307.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___1031_71307.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___1031_71307.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___1031_71307.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___1031_71307.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (uu___1031_71307.FStar_Tactics_Types.local_state)
           }  in
         let uu____71309 = set ps1  in
         bind uu____71309
           (fun uu____71314  ->
              let uu____71315 = FStar_BigInt.of_int_fs n1  in ret uu____71315))
  
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
              let uu____71353 = env.FStar_TypeChecker_Env.universe_of env phi
                 in
              FStar_Syntax_Util.mk_squash uu____71353 phi  in
            let uu____71354 = new_uvar reason env typ  in
            bind uu____71354
              (fun uu____71369  ->
                 match uu____71369 with
                 | (uu____71376,ctx_uvar) ->
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
             (fun uu____71423  ->
                let uu____71424 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____71424)
             (fun uu____71429  ->
                let e1 =
                  let uu___1049_71431 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1049_71431.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1049_71431.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1049_71431.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1049_71431.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1049_71431.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1049_71431.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1049_71431.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1049_71431.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1049_71431.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1049_71431.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1049_71431.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1049_71431.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1049_71431.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1049_71431.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1049_71431.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1049_71431.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1049_71431.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1049_71431.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1049_71431.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1049_71431.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1049_71431.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1049_71431.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1049_71431.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1049_71431.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1049_71431.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1049_71431.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1049_71431.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1049_71431.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1049_71431.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1049_71431.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1049_71431.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1049_71431.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1049_71431.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1049_71431.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1049_71431.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1049_71431.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1049_71431.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1049_71431.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1049_71431.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1049_71431.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1049_71431.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1049_71431.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___1053_71443  ->
                     match () with
                     | () ->
                         let uu____71452 =
                           FStar_TypeChecker_TcTerm.type_of_tot_term e1 t  in
                         ret uu____71452) ()
                with
                | FStar_Errors.Err (uu____71479,msg) ->
                    let uu____71483 = tts e1 t  in
                    let uu____71485 =
                      let uu____71487 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____71487
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____71483 uu____71485 msg
                | FStar_Errors.Error (uu____71497,msg,uu____71499) ->
                    let uu____71502 = tts e1 t  in
                    let uu____71504 =
                      let uu____71506 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____71506
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____71502 uu____71504 msg))
  
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
             (fun uu____71559  ->
                let uu____71560 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc_ghost(%s)\n" uu____71560)
             (fun uu____71565  ->
                let e1 =
                  let uu___1070_71567 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1070_71567.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1070_71567.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1070_71567.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1070_71567.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1070_71567.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1070_71567.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1070_71567.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1070_71567.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1070_71567.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1070_71567.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1070_71567.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1070_71567.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1070_71567.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1070_71567.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1070_71567.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1070_71567.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1070_71567.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1070_71567.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1070_71567.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1070_71567.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1070_71567.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1070_71567.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1070_71567.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1070_71567.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1070_71567.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1070_71567.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1070_71567.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1070_71567.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1070_71567.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1070_71567.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1070_71567.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1070_71567.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1070_71567.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1070_71567.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1070_71567.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1070_71567.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1070_71567.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1070_71567.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1070_71567.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1070_71567.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1070_71567.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1070_71567.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___1074_71582  ->
                     match () with
                     | () ->
                         let uu____71591 =
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e1 t
                            in
                         (match uu____71591 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____71629,msg) ->
                    let uu____71633 = tts e1 t  in
                    let uu____71635 =
                      let uu____71637 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____71637
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____71633 uu____71635 msg
                | FStar_Errors.Error (uu____71647,msg,uu____71649) ->
                    let uu____71652 = tts e1 t  in
                    let uu____71654 =
                      let uu____71656 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____71656
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____71652 uu____71654 msg))
  
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
             (fun uu____71709  ->
                let uu____71710 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____71710)
             (fun uu____71716  ->
                let e1 =
                  let uu___1095_71718 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1095_71718.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1095_71718.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1095_71718.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1095_71718.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1095_71718.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1095_71718.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1095_71718.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1095_71718.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1095_71718.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1095_71718.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1095_71718.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1095_71718.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1095_71718.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1095_71718.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1095_71718.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1095_71718.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1095_71718.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1095_71718.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1095_71718.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1095_71718.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1095_71718.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1095_71718.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1095_71718.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1095_71718.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1095_71718.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1095_71718.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1095_71718.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1095_71718.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1095_71718.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1095_71718.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1095_71718.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1095_71718.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1095_71718.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1095_71718.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1095_71718.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1095_71718.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1095_71718.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1095_71718.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1095_71718.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1095_71718.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1095_71718.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1095_71718.FStar_TypeChecker_Env.nbe)
                  }  in
                let e2 =
                  let uu___1098_71721 = e1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1098_71721.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1098_71721.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1098_71721.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1098_71721.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1098_71721.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1098_71721.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1098_71721.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1098_71721.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1098_71721.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1098_71721.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1098_71721.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1098_71721.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1098_71721.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1098_71721.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1098_71721.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1098_71721.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1098_71721.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1098_71721.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1098_71721.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1098_71721.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1098_71721.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1098_71721.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1098_71721.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1098_71721.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___1098_71721.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1098_71721.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1098_71721.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1098_71721.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1098_71721.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1098_71721.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1098_71721.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1098_71721.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1098_71721.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1098_71721.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1098_71721.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1098_71721.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1098_71721.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1098_71721.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1098_71721.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1098_71721.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1098_71721.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1098_71721.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___1102_71736  ->
                     match () with
                     | () ->
                         let uu____71745 =
                           FStar_TypeChecker_TcTerm.tc_term e2 t  in
                         (match uu____71745 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____71783,msg) ->
                    let uu____71787 = tts e2 t  in
                    let uu____71789 =
                      let uu____71791 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____71791
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____71787 uu____71789 msg
                | FStar_Errors.Error (uu____71801,msg,uu____71803) ->
                    let uu____71806 = tts e2 t  in
                    let uu____71808 =
                      let uu____71810 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____71810
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____71806 uu____71808 msg))
  
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
  fun uu____71844  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___1127_71863 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___1127_71863.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___1127_71863.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___1127_71863.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___1127_71863.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___1127_71863.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___1127_71863.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___1127_71863.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___1127_71863.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___1127_71863.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___1127_71863.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___1127_71863.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___1127_71863.FStar_Tactics_Types.local_state)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____71888 = get_guard_policy ()  in
      bind uu____71888
        (fun old_pol  ->
           let uu____71894 = set_guard_policy pol  in
           bind uu____71894
             (fun uu____71898  ->
                bind t
                  (fun r  ->
                     let uu____71902 = set_guard_policy old_pol  in
                     bind uu____71902 (fun uu____71906  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____71910 = let uu____71915 = cur_goal ()  in trytac uu____71915  in
  bind uu____71910
    (fun uu___609_71922  ->
       match uu___609_71922 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____71928 = FStar_Options.peek ()  in ret uu____71928)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        mlog
          (fun uu____71953  ->
             let uu____71954 = FStar_TypeChecker_Rel.guard_to_string e g  in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason
               uu____71954)
          (fun uu____71959  ->
             let uu____71960 =
               add_implicits g.FStar_TypeChecker_Env.implicits  in
             bind uu____71960
               (fun uu____71964  ->
                  bind getopts
                    (fun opts  ->
                       let uu____71968 =
                         let uu____71969 =
                           FStar_TypeChecker_Rel.simplify_guard e g  in
                         uu____71969.FStar_TypeChecker_Env.guard_f  in
                       match uu____71968 with
                       | FStar_TypeChecker_Common.Trivial  -> ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____71973 = istrivial e f  in
                           if uu____71973
                           then ret ()
                           else
                             bind get
                               (fun ps  ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop  ->
                                      ((let uu____71986 =
                                          let uu____71992 =
                                            let uu____71994 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g
                                               in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____71994
                                             in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____71992)
                                           in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____71986);
                                       ret ())
                                  | FStar_Tactics_Types.Goal  ->
                                      mlog
                                        (fun uu____72000  ->
                                           let uu____72001 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____72001)
                                        (fun uu____72006  ->
                                           let uu____72007 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____72007
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___1156_72015 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___1156_72015.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___1156_72015.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___1156_72015.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___1156_72015.FStar_Tactics_Types.label)
                                                  }  in
                                                push_goals [goal1]))
                                  | FStar_Tactics_Types.SMT  ->
                                      mlog
                                        (fun uu____72019  ->
                                           let uu____72020 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____72020)
                                        (fun uu____72025  ->
                                           let uu____72026 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____72026
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___1163_72034 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___1163_72034.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___1163_72034.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___1163_72034.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___1163_72034.FStar_Tactics_Types.label)
                                                  }  in
                                                push_smt_goals [goal1]))
                                  | FStar_Tactics_Types.Force  ->
                                      mlog
                                        (fun uu____72038  ->
                                           let uu____72039 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____72039)
                                        (fun uu____72043  ->
                                           try
                                             (fun uu___1170_72048  ->
                                                match () with
                                                | () ->
                                                    let uu____72051 =
                                                      let uu____72053 =
                                                        let uu____72055 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____72055
                                                         in
                                                      Prims.op_Negation
                                                        uu____72053
                                                       in
                                                    if uu____72051
                                                    then
                                                      mlog
                                                        (fun uu____72062  ->
                                                           let uu____72063 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g
                                                              in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____72063)
                                                        (fun uu____72067  ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else ret ()) ()
                                           with
                                           | uu___1169_72072 ->
                                               mlog
                                                 (fun uu____72077  ->
                                                    let uu____72078 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g
                                                       in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____72078)
                                                 (fun uu____72082  ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____72094 =
      let uu____72097 = cur_goal ()  in
      bind uu____72097
        (fun goal  ->
           let uu____72103 =
             let uu____72112 = FStar_Tactics_Types.goal_env goal  in
             __tc_lax uu____72112 t  in
           bind uu____72103
             (fun uu____72123  ->
                match uu____72123 with
                | (uu____72132,typ,uu____72134) -> ret typ))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____72094
  
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
            let uu____72174 = mk_irrelevant_goal reason env phi opts label1
               in
            bind uu____72174 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____72186  ->
    let uu____72189 = cur_goal ()  in
    bind uu____72189
      (fun goal  ->
         let uu____72195 =
           let uu____72197 = FStar_Tactics_Types.goal_env goal  in
           let uu____72198 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____72197 uu____72198  in
         if uu____72195
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____72204 =
              let uu____72206 = FStar_Tactics_Types.goal_env goal  in
              let uu____72207 = FStar_Tactics_Types.goal_type goal  in
              tts uu____72206 uu____72207  in
            fail1 "Not a trivial goal: %s" uu____72204))
  
let divide : 'a 'b . FStar_BigInt.t -> 'a tac -> 'b tac -> ('a * 'b) tac =
  fun n1  ->
    fun l  ->
      fun r  ->
        bind get
          (fun p  ->
             let uu____72258 =
               try
                 (fun uu___1226_72281  ->
                    match () with
                    | () ->
                        let uu____72292 =
                          let uu____72301 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____72301
                            p.FStar_Tactics_Types.goals
                           in
                        ret uu____72292) ()
               with | uu___1225_72312 -> fail "divide: not enough goals"  in
             bind uu____72258
               (fun uu____72349  ->
                  match uu____72349 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___1208_72375 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___1208_72375.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___1208_72375.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___1208_72375.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___1208_72375.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___1208_72375.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___1208_72375.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___1208_72375.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___1208_72375.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___1208_72375.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___1208_72375.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___1208_72375.FStar_Tactics_Types.local_state)
                        }  in
                      let uu____72376 = set lp  in
                      bind uu____72376
                        (fun uu____72384  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___1214_72400 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___1214_72400.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___1214_72400.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___1214_72400.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___1214_72400.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___1214_72400.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___1214_72400.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___1214_72400.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___1214_72400.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___1214_72400.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___1214_72400.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___1214_72400.FStar_Tactics_Types.local_state)
                                       }  in
                                     let uu____72401 = set rp  in
                                     bind uu____72401
                                       (fun uu____72409  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___1220_72425 =
                                                        rp'  in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___1220_72425.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___1220_72425.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___1220_72425.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___1220_72425.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___1220_72425.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___1220_72425.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___1220_72425.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___1220_72425.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___1220_72425.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___1220_72425.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___1220_72425.FStar_Tactics_Types.local_state)
                                                      }  in
                                                    let uu____72426 = set p'
                                                       in
                                                    bind uu____72426
                                                      (fun uu____72434  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____72440 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____72462 = divide FStar_BigInt.one f idtac  in
    bind uu____72462
      (fun uu____72475  -> match uu____72475 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____72513::uu____72514 ->
             let uu____72517 =
               let uu____72526 = map tau  in
               divide FStar_BigInt.one tau uu____72526  in
             bind uu____72517
               (fun uu____72544  ->
                  match uu____72544 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____72586 =
        bind t1
          (fun uu____72591  ->
             let uu____72592 = map t2  in
             bind uu____72592 (fun uu____72600  -> ret ()))
         in
      focus uu____72586
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____72610  ->
    let uu____72613 =
      let uu____72616 = cur_goal ()  in
      bind uu____72616
        (fun goal  ->
           let uu____72625 =
             let uu____72632 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____72632  in
           match uu____72625 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____72641 =
                 let uu____72643 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____72643  in
               if uu____72641
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____72652 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____72652 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____72666 = new_uvar "intro" env' typ'  in
                  bind uu____72666
                    (fun uu____72683  ->
                       match uu____72683 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c))
                              in
                           let uu____72707 = set_solution goal sol  in
                           bind uu____72707
                             (fun uu____72713  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                    goal.FStar_Tactics_Types.label
                                   in
                                let uu____72715 =
                                  let uu____72718 = bnorm_goal g  in
                                  replace_cur uu____72718  in
                                bind uu____72715 (fun uu____72720  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____72725 =
                 let uu____72727 = FStar_Tactics_Types.goal_env goal  in
                 let uu____72728 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____72727 uu____72728  in
               fail1 "goal is not an arrow (%s)" uu____72725)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____72613
  
let (intro_rec :
  unit -> (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder) tac) =
  fun uu____72746  ->
    let uu____72753 = cur_goal ()  in
    bind uu____72753
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____72772 =
            let uu____72779 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____72779  in
          match uu____72772 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____72792 =
                let uu____72794 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____72794  in
              if uu____72792
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____72811 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____72811
                    in
                 let bs =
                   let uu____72822 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____72822; b]  in
                 let env' =
                   let uu____72848 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____72848 bs  in
                 let uu____72849 =
                   let uu____72856 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____72856  in
                 bind uu____72849
                   (fun uu____72876  ->
                      match uu____72876 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____72890 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____72893 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____72890
                              FStar_Parser_Const.effect_Tot_lid uu____72893
                              [] FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____72911 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____72911 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____72933 =
                                   let uu____72934 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____72934.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____72933
                                  in
                               let uu____72950 = set_solution goal tm  in
                               bind uu____72950
                                 (fun uu____72959  ->
                                    let uu____72960 =
                                      let uu____72963 =
                                        bnorm_goal
                                          (let uu___1291_72966 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___1291_72966.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___1291_72966.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___1291_72966.FStar_Tactics_Types.is_guard);
                                             FStar_Tactics_Types.label =
                                               (uu___1291_72966.FStar_Tactics_Types.label)
                                           })
                                         in
                                      replace_cur uu____72963  in
                                    bind uu____72960
                                      (fun uu____72973  ->
                                         let uu____72974 =
                                           let uu____72979 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____72979, b)  in
                                         ret uu____72974)))))
          | FStar_Pervasives_Native.None  ->
              let uu____72988 =
                let uu____72990 = FStar_Tactics_Types.goal_env goal  in
                let uu____72991 = FStar_Tactics_Types.goal_type goal  in
                tts uu____72990 uu____72991  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____72988))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____73011 = cur_goal ()  in
    bind uu____73011
      (fun goal  ->
         mlog
           (fun uu____73018  ->
              let uu____73019 =
                let uu____73021 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____73021  in
              FStar_Util.print1 "norm: witness = %s\n" uu____73019)
           (fun uu____73027  ->
              let steps =
                let uu____73031 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____73031
                 in
              let t =
                let uu____73035 = FStar_Tactics_Types.goal_env goal  in
                let uu____73036 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____73035 uu____73036  in
              let uu____73037 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____73037))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____73062 =
          bind get
            (fun ps  ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
                 | g::uu____73070 -> g.FStar_Tactics_Types.opts
                 | uu____73073 -> FStar_Options.peek ()  in
               mlog
                 (fun uu____73078  ->
                    let uu____73079 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____73079)
                 (fun uu____73084  ->
                    let uu____73085 = __tc_lax e t  in
                    bind uu____73085
                      (fun uu____73106  ->
                         match uu____73106 with
                         | (t1,uu____73116,uu____73117) ->
                             let steps =
                               let uu____73121 =
                                 FStar_TypeChecker_Normalize.tr_norm_steps s
                                  in
                               FStar_List.append
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu____73121
                                in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1
                                in
                             mlog
                               (fun uu____73127  ->
                                  let uu____73128 =
                                    FStar_Syntax_Print.term_to_string t2  in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____73128)
                               (fun uu____73132  -> ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____73062
  
let (refine_intro : unit -> unit tac) =
  fun uu____73145  ->
    let uu____73148 =
      let uu____73151 = cur_goal ()  in
      bind uu____73151
        (fun g  ->
           let uu____73158 =
             let uu____73169 = FStar_Tactics_Types.goal_env g  in
             let uu____73170 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____73169
               uu____73170
              in
           match uu____73158 with
           | (uu____73173,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____73199 =
                 let uu____73204 =
                   let uu____73209 =
                     let uu____73210 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____73210]  in
                   FStar_Syntax_Subst.open_term uu____73209 phi  in
                 match uu____73204 with
                 | (bvs,phi1) ->
                     let uu____73235 =
                       let uu____73236 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____73236  in
                     (uu____73235, phi1)
                  in
               (match uu____73199 with
                | (bv1,phi1) ->
                    let uu____73255 =
                      let uu____73258 = FStar_Tactics_Types.goal_env g  in
                      let uu____73259 =
                        let uu____73260 =
                          let uu____73263 =
                            let uu____73264 =
                              let uu____73271 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____73271)  in
                            FStar_Syntax_Syntax.NT uu____73264  in
                          [uu____73263]  in
                        FStar_Syntax_Subst.subst uu____73260 phi1  in
                      mk_irrelevant_goal "refine_intro refinement"
                        uu____73258 uu____73259 g.FStar_Tactics_Types.opts
                        g.FStar_Tactics_Types.label
                       in
                    bind uu____73255
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____73280  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____73148
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____73303 = cur_goal ()  in
      bind uu____73303
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____73312 = FStar_Tactics_Types.goal_env goal  in
               let uu____73313 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____73312 uu____73313
             else FStar_Tactics_Types.goal_env goal  in
           let uu____73316 = __tc env t  in
           bind uu____73316
             (fun uu____73335  ->
                match uu____73335 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____73350  ->
                         let uu____73351 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____73353 =
                           let uu____73355 =
                             FStar_Tactics_Types.goal_env goal  in
                           FStar_TypeChecker_Rel.guard_to_string uu____73355
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____73351 uu____73353)
                      (fun uu____73359  ->
                         let uu____73360 =
                           let uu____73363 =
                             FStar_Tactics_Types.goal_env goal  in
                           proc_guard "__exact typing" uu____73363 guard  in
                         bind uu____73360
                           (fun uu____73366  ->
                              mlog
                                (fun uu____73370  ->
                                   let uu____73371 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____73373 =
                                     let uu____73375 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____73375
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____73371 uu____73373)
                                (fun uu____73379  ->
                                   let uu____73380 =
                                     let uu____73384 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____73385 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____73384 typ uu____73385  in
                                   bind uu____73380
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____73395 =
                                             let uu____73397 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____73397 t1  in
                                           let uu____73398 =
                                             let uu____73400 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____73400 typ  in
                                           let uu____73401 =
                                             let uu____73403 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____73404 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____73403 uu____73404  in
                                           let uu____73405 =
                                             let uu____73407 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____73408 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____73407 uu____73408  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____73395 uu____73398
                                             uu____73401 uu____73405)))))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun try_refine  ->
    fun set_expected_typ1  ->
      fun tm  ->
        let uu____73434 =
          mlog
            (fun uu____73439  ->
               let uu____73440 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____73440)
            (fun uu____73445  ->
               let uu____73446 =
                 let uu____73453 = __exact_now set_expected_typ1 tm  in
                 catch uu____73453  in
               bind uu____73446
                 (fun uu___611_73462  ->
                    match uu___611_73462 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        traise e
                    | FStar_Util.Inl e ->
                        mlog
                          (fun uu____73473  ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____73477  ->
                             let uu____73478 =
                               let uu____73485 =
                                 let uu____73488 =
                                   norm [FStar_Syntax_Embeddings.Delta]  in
                                 bind uu____73488
                                   (fun uu____73493  ->
                                      let uu____73494 = refine_intro ()  in
                                      bind uu____73494
                                        (fun uu____73498  ->
                                           __exact_now set_expected_typ1 tm))
                                  in
                               catch uu____73485  in
                             bind uu____73478
                               (fun uu___610_73505  ->
                                  match uu___610_73505 with
                                  | FStar_Util.Inr r ->
                                      mlog
                                        (fun uu____73514  ->
                                           FStar_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu____73517  -> ret ())
                                  | FStar_Util.Inl uu____73518 ->
                                      mlog
                                        (fun uu____73520  ->
                                           FStar_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu____73523  -> traise e)))))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____73434
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____73575 = f x  in
          bind uu____73575
            (fun y  ->
               let uu____73583 = mapM f xs  in
               bind uu____73583 (fun ys  -> ret (y :: ys)))
  
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
          let uu____73655 = do_unify e ty1 ty2  in
          bind uu____73655
            (fun uu___612_73669  ->
               if uu___612_73669
               then ret acc
               else
                 (let uu____73689 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____73689 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____73710 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____73712 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____73710
                        uu____73712
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____73729 =
                        let uu____73731 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____73731  in
                      if uu____73729
                      then fail "Codomain is effectful"
                      else
                        (let uu____73755 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____73755
                           (fun uu____73782  ->
                              match uu____73782 with
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
      let uu____73872 =
        mlog
          (fun uu____73877  ->
             let uu____73878 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_apply: tm = %s\n" uu____73878)
          (fun uu____73883  ->
             let uu____73884 = cur_goal ()  in
             bind uu____73884
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____73892 = __tc e tm  in
                  bind uu____73892
                    (fun uu____73913  ->
                       match uu____73913 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____73926 =
                             let uu____73937 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____73937  in
                           bind uu____73926
                             (fun uvs  ->
                                let fix_qual q =
                                  match q with
                                  | FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Meta uu____73975)
                                      ->
                                      FStar_Pervasives_Native.Some
                                        (FStar_Syntax_Syntax.Implicit false)
                                  | uu____73979 -> q  in
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____74002  ->
                                       fun w  ->
                                         match uu____74002 with
                                         | (uvt,q,uu____74020) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, (fix_qual q))]) uvs tm1
                                   in
                                let uvset =
                                  let uu____74052 =
                                    FStar_Syntax_Free.new_uv_set ()  in
                                  FStar_List.fold_right
                                    (fun uu____74069  ->
                                       fun s  ->
                                         match uu____74069 with
                                         | (uu____74081,uu____74082,uv) ->
                                             let uu____74084 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                in
                                             FStar_Util.set_union s
                                               uu____74084) uvs uu____74052
                                   in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset  in
                                let uu____74094 = solve' goal w  in
                                bind uu____74094
                                  (fun uu____74099  ->
                                     let uu____74100 =
                                       mapM
                                         (fun uu____74117  ->
                                            match uu____74117 with
                                            | (uvt,q,uv) ->
                                                let uu____74129 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                   in
                                                (match uu____74129 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____74134 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____74135 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv)
                                                        in
                                                     if uu____74135
                                                     then ret ()
                                                     else
                                                       (let uu____74142 =
                                                          let uu____74145 =
                                                            bnorm_goal
                                                              (let uu___1452_74148
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___1452_74148.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___1452_74148.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false;
                                                                 FStar_Tactics_Types.label
                                                                   =
                                                                   (uu___1452_74148.FStar_Tactics_Types.label)
                                                               })
                                                             in
                                                          [uu____74145]  in
                                                        add_goals uu____74142)))
                                         uvs
                                        in
                                     bind uu____74100
                                       (fun uu____74153  ->
                                          proc_guard "apply guard" e guard))))))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____73872
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____74181 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____74181
    then
      let uu____74190 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____74205 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____74258 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____74190 with
      | (pre,post) ->
          let post1 =
            let uu____74291 =
              let uu____74302 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____74302]  in
            FStar_Syntax_Util.mk_app post uu____74291  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____74333 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____74333
       then
         let uu____74342 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____74342
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
            let uu____74421 = f x e  in
            bind uu____74421 (fun e'  -> fold_left f e' xs1)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____74436 =
      let uu____74439 =
        bind get
          (fun ps  ->
             mlog
               (fun uu____74446  ->
                  let uu____74447 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____74447)
               (fun uu____74453  ->
                  let is_unit_t t =
                    let uu____74461 =
                      let uu____74462 = FStar_Syntax_Subst.compress t  in
                      uu____74462.FStar_Syntax_Syntax.n  in
                    match uu____74461 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____74468 -> false  in
                  let uu____74470 = cur_goal ()  in
                  bind uu____74470
                    (fun goal  ->
                       let uu____74476 =
                         let uu____74485 = FStar_Tactics_Types.goal_env goal
                            in
                         __tc uu____74485 tm  in
                       bind uu____74476
                         (fun uu____74500  ->
                            match uu____74500 with
                            | (tm1,t,guard) ->
                                let uu____74512 =
                                  FStar_Syntax_Util.arrow_formals_comp t  in
                                (match uu____74512 with
                                 | (bs,comp) ->
                                     let uu____74545 = lemma_or_sq comp  in
                                     (match uu____74545 with
                                      | FStar_Pervasives_Native.None  ->
                                          fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre,post) ->
                                          let uu____74565 =
                                            fold_left
                                              (fun uu____74627  ->
                                                 fun uu____74628  ->
                                                   match (uu____74627,
                                                           uu____74628)
                                                   with
                                                   | ((b,aq),(uvs,imps,subst1))
                                                       ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst1
                                                           b.FStar_Syntax_Syntax.sort
                                                          in
                                                       let uu____74779 =
                                                         is_unit_t b_t  in
                                                       if uu____74779
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
                                                         (let uu____74902 =
                                                            let uu____74909 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            new_uvar
                                                              "apply_lemma"
                                                              uu____74909 b_t
                                                             in
                                                          bind uu____74902
                                                            (fun uu____74940 
                                                               ->
                                                               match uu____74940
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
                                          bind uu____74565
                                            (fun uu____75126  ->
                                               match uu____75126 with
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
                                                   let uu____75214 =
                                                     let uu____75218 =
                                                       FStar_Tactics_Types.goal_env
                                                         goal
                                                        in
                                                     let uu____75219 =
                                                       FStar_Syntax_Util.mk_squash
                                                         FStar_Syntax_Syntax.U_zero
                                                         post1
                                                        in
                                                     let uu____75220 =
                                                       FStar_Tactics_Types.goal_type
                                                         goal
                                                        in
                                                     do_unify uu____75218
                                                       uu____75219
                                                       uu____75220
                                                      in
                                                   bind uu____75214
                                                     (fun b  ->
                                                        if
                                                          Prims.op_Negation b
                                                        then
                                                          let uu____75231 =
                                                            let uu____75233 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            tts uu____75233
                                                              tm1
                                                             in
                                                          let uu____75234 =
                                                            let uu____75236 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            let uu____75237 =
                                                              FStar_Syntax_Util.mk_squash
                                                                FStar_Syntax_Syntax.U_zero
                                                                post1
                                                               in
                                                            tts uu____75236
                                                              uu____75237
                                                             in
                                                          let uu____75238 =
                                                            let uu____75240 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            let uu____75241 =
                                                              FStar_Tactics_Types.goal_type
                                                                goal
                                                               in
                                                            tts uu____75240
                                                              uu____75241
                                                             in
                                                          fail3
                                                            "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                            uu____75231
                                                            uu____75234
                                                            uu____75238
                                                        else
                                                          (let uu____75245 =
                                                             solve' goal
                                                               FStar_Syntax_Util.exp_unit
                                                              in
                                                           bind uu____75245
                                                             (fun uu____75253
                                                                 ->
                                                                let is_free_uvar
                                                                  uv t1 =
                                                                  let free_uvars
                                                                    =
                                                                    let uu____75279
                                                                    =
                                                                    let uu____75282
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____75282
                                                                     in
                                                                    FStar_List.map
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____75279
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
                                                                    let uu____75318
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____75318)
                                                                    goals
                                                                   in
                                                                let checkone
                                                                  t1 goals =
                                                                  let uu____75335
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                  match uu____75335
                                                                  with
                                                                  | (hd1,uu____75354)
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____75381)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____75398
                                                                    -> false)
                                                                   in
                                                                let uu____75400
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
                                                                    let uu____75443
                                                                    = imp  in
                                                                    match uu____75443
                                                                    with
                                                                    | 
                                                                    (term,ctx_uvar)
                                                                    ->
                                                                    let uu____75454
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____75454
                                                                    with
                                                                    | 
                                                                    (hd1,uu____75476)
                                                                    ->
                                                                    let uu____75501
                                                                    =
                                                                    let uu____75502
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____75502.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____75501
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____75510)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___1562_75530
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___1562_75530.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___1562_75530.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___1562_75530.FStar_Tactics_Types.is_guard);
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___1562_75530.FStar_Tactics_Types.label)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____75533
                                                                    ->
                                                                    mlog
                                                                    (fun
                                                                    uu____75539
                                                                     ->
                                                                    let uu____75540
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                                                     in
                                                                    let uu____75542
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____75540
                                                                    uu____75542)
                                                                    (fun
                                                                    uu____75549
                                                                     ->
                                                                    let env =
                                                                    let uu___1567_75551
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___1567_75551.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1567_75551.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1567_75551.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___1567_75551.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1567_75551.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1567_75551.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1567_75551.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1567_75551.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___1567_75551.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___1567_75551.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___1567_75551.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1567_75551.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1567_75551.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1567_75551.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1567_75551.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1567_75551.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1567_75551.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1567_75551.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___1567_75551.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___1567_75551.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___1567_75551.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1567_75551.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1567_75551.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1567_75551.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1567_75551.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1567_75551.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1567_75551.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1567_75551.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1567_75551.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1567_75551.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1567_75551.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1567_75551.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1567_75551.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1567_75551.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___1567_75551.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1567_75551.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1567_75551.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___1567_75551.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1567_75551.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1567_75551.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1567_75551.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1567_75551.FStar_TypeChecker_Env.nbe)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let uu____75554
                                                                    =
                                                                    let uu____75557
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____75561
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
                                                                    let uu____75563
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____75561
                                                                    uu____75563
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____75569
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    uu____75557
                                                                    uu____75569
                                                                    g_typ  in
                                                                    bind
                                                                    uu____75554
                                                                    (fun
                                                                    uu____75573
                                                                     ->
                                                                    ret []))))))
                                                                   in
                                                                bind
                                                                  uu____75400
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
                                                                    let uu____75637
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____75637
                                                                    then
                                                                    let uu____75642
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____75642
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
                                                                    let uu____75657
                                                                    =
                                                                    let uu____75659
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____75659
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____75657)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____75660
                                                                    =
                                                                    let uu____75663
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____75663
                                                                    guard  in
                                                                    bind
                                                                    uu____75660
                                                                    (fun
                                                                    uu____75667
                                                                     ->
                                                                    let uu____75668
                                                                    =
                                                                    let uu____75671
                                                                    =
                                                                    let uu____75673
                                                                    =
                                                                    let uu____75675
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____75676
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____75675
                                                                    uu____75676
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____75673
                                                                     in
                                                                    if
                                                                    uu____75671
                                                                    then
                                                                    let uu____75680
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____75680
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    goal.FStar_Tactics_Types.label
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____75668
                                                                    (fun
                                                                    uu____75685
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2)))))))))))))
         in
      focus uu____74439  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____74436
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____75709 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____75709 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____75719::(e1,uu____75721)::(e2,uu____75723)::[])) when
        (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) ||
          (FStar_Ident.lid_equals l FStar_Parser_Const.c_eq2_lid)
        -> FStar_Pervasives_Native.Some (e1, e2)
    | uu____75784 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____75809 = destruct_eq' typ  in
    match uu____75809 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____75839 = FStar_Syntax_Util.un_squash typ  in
        (match uu____75839 with
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
        let uu____75908 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____75908 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', bv', [])
            else
              (let uu____75966 = aux e'  in
               FStar_Util.map_opt uu____75966
                 (fun uu____75997  ->
                    match uu____75997 with
                    | (e'',bv,bvs) -> (e'', bv, (bv' :: bvs))))
         in
      let uu____76023 = aux e  in
      FStar_Util.map_opt uu____76023
        (fun uu____76054  ->
           match uu____76054 with
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
          let uu____76128 =
            let uu____76139 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____76139  in
          FStar_Util.map_opt uu____76128
            (fun uu____76157  ->
               match uu____76157 with
               | (e0,b11,bvs) ->
                   let s1 bv =
                     let uu___1640_76179 = bv  in
                     let uu____76180 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___1640_76179.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___1640_76179.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____76180
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___1644_76188 =
                       g.FStar_Tactics_Types.goal_ctx_uvar  in
                     let uu____76189 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____76198 =
                       let uu____76201 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____76201  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___1644_76188.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____76189;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____76198;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___1644_76188.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___1644_76188.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___1644_76188.FStar_Syntax_Syntax.ctx_uvar_range);
                       FStar_Syntax_Syntax.ctx_uvar_meta =
                         (uu___1644_76188.FStar_Syntax_Syntax.ctx_uvar_meta)
                     }  in
                   let uu___1647_76202 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1647_76202.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___1647_76202.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___1647_76202.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1647_76202.FStar_Tactics_Types.label)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____76213 =
      let uu____76216 = cur_goal ()  in
      bind uu____76216
        (fun goal  ->
           let uu____76224 = h  in
           match uu____76224 with
           | (bv,uu____76228) ->
               mlog
                 (fun uu____76236  ->
                    let uu____76237 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____76239 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____76237
                      uu____76239)
                 (fun uu____76244  ->
                    let uu____76245 =
                      let uu____76256 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____76256  in
                    match uu____76245 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                        let uu____76283 =
                          destruct_eq bv1.FStar_Syntax_Syntax.sort  in
                        (match uu____76283 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____76298 =
                               let uu____76299 =
                                 FStar_Syntax_Subst.compress x  in
                               uu____76299.FStar_Syntax_Syntax.n  in
                             (match uu____76298 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv2 =
                                    let uu___1670_76316 = bv2  in
                                    let uu____76317 =
                                      FStar_Syntax_Subst.subst s
                                        bv2.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1670_76316.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1670_76316.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____76317
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv1 :: bvs1)  in
                                  let new_goal =
                                    let uu___1674_76325 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____76326 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____76335 =
                                      let uu____76338 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____76338
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___1674_76325.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____76326;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____76335;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___1674_76325.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___1674_76325.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___1674_76325.FStar_Syntax_Syntax.ctx_uvar_range);
                                      FStar_Syntax_Syntax.ctx_uvar_meta =
                                        (uu___1674_76325.FStar_Syntax_Syntax.ctx_uvar_meta)
                                    }  in
                                  replace_cur
                                    (let uu___1677_76341 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___1677_76341.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___1677_76341.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___1677_76341.FStar_Tactics_Types.is_guard);
                                       FStar_Tactics_Types.label =
                                         (uu___1677_76341.FStar_Tactics_Types.label)
                                     })
                              | uu____76342 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____76344 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____76213
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____76374 =
        let uu____76377 = cur_goal ()  in
        bind uu____76377
          (fun goal  ->
             let uu____76388 = b  in
             match uu____76388 with
             | (bv,uu____76392) ->
                 let bv' =
                   let uu____76398 =
                     let uu___1688_76399 = bv  in
                     let uu____76400 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____76400;
                       FStar_Syntax_Syntax.index =
                         (uu___1688_76399.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___1688_76399.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____76398  in
                 let s1 =
                   let uu____76405 =
                     let uu____76406 =
                       let uu____76413 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____76413)  in
                     FStar_Syntax_Syntax.NT uu____76406  in
                   [uu____76405]  in
                 let uu____76418 = subst_goal bv bv' s1 goal  in
                 (match uu____76418 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____76374
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____76440 =
      let uu____76443 = cur_goal ()  in
      bind uu____76443
        (fun goal  ->
           let uu____76452 = b  in
           match uu____76452 with
           | (bv,uu____76456) ->
               let uu____76461 =
                 let uu____76472 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____76472  in
               (match uu____76461 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                    let uu____76499 = FStar_Syntax_Util.type_u ()  in
                    (match uu____76499 with
                     | (ty,u) ->
                         let uu____76508 = new_uvar "binder_retype" e0 ty  in
                         bind uu____76508
                           (fun uu____76527  ->
                              match uu____76527 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___1712_76537 = bv1  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1712_76537.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1712_76537.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____76541 =
                                      let uu____76542 =
                                        let uu____76549 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv1, uu____76549)  in
                                      FStar_Syntax_Syntax.NT uu____76542  in
                                    [uu____76541]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___1717_76561 = b1  in
                                         let uu____76562 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___1717_76561.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___1717_76561.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____76562
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____76569  ->
                                       let new_goal =
                                         let uu____76571 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____76572 =
                                           let uu____76573 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____76573
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____76571 uu____76572
                                          in
                                       let uu____76574 = add_goals [new_goal]
                                          in
                                       bind uu____76574
                                         (fun uu____76579  ->
                                            let uu____76580 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv1.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____76580
                                              goal.FStar_Tactics_Types.opts
                                              goal.FStar_Tactics_Types.label))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____76440
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____76606 =
        let uu____76609 = cur_goal ()  in
        bind uu____76609
          (fun goal  ->
             let uu____76618 = b  in
             match uu____76618 with
             | (bv,uu____76622) ->
                 let uu____76627 =
                   let uu____76638 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____76638  in
                 (match uu____76627 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                      let steps =
                        let uu____76668 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____76668
                         in
                      let sort' =
                        normalize steps e0 bv1.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___1738_76673 = bv1  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___1738_76673.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___1738_76673.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____76675 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____76675))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____76606
  
let (revert : unit -> unit tac) =
  fun uu____76688  ->
    let uu____76691 = cur_goal ()  in
    bind uu____76691
      (fun goal  ->
         let uu____76697 =
           let uu____76704 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____76704  in
         match uu____76697 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____76721 =
                 let uu____76724 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____76724  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____76721
                in
             let uu____76739 = new_uvar "revert" env' typ'  in
             bind uu____76739
               (fun uu____76755  ->
                  match uu____76755 with
                  | (r,u_r) ->
                      let uu____76764 =
                        let uu____76767 =
                          let uu____76768 =
                            let uu____76769 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____76769.FStar_Syntax_Syntax.pos  in
                          let uu____76772 =
                            let uu____76777 =
                              let uu____76778 =
                                let uu____76787 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____76787  in
                              [uu____76778]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____76777  in
                          uu____76772 FStar_Pervasives_Native.None
                            uu____76768
                           in
                        set_solution goal uu____76767  in
                      bind uu____76764
                        (fun uu____76808  ->
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
      let uu____76822 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____76822
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____76838 = cur_goal ()  in
    bind uu____76838
      (fun goal  ->
         mlog
           (fun uu____76846  ->
              let uu____76847 = FStar_Syntax_Print.binder_to_string b  in
              let uu____76849 =
                let uu____76851 =
                  let uu____76853 =
                    let uu____76862 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____76862  in
                  FStar_All.pipe_right uu____76853 FStar_List.length  in
                FStar_All.pipe_right uu____76851 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____76847 uu____76849)
           (fun uu____76883  ->
              let uu____76884 =
                let uu____76895 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____76895  in
              match uu____76884 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bv1,bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____76940 =
                          free_in bv1 bv'.FStar_Syntax_Syntax.sort  in
                        if uu____76940
                        then
                          let uu____76945 =
                            let uu____76947 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____76947
                             in
                          fail uu____76945
                        else check1 bvs2
                     in
                  let uu____76952 =
                    let uu____76954 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv1 uu____76954  in
                  if uu____76952
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____76961 = check1 bvs  in
                     bind uu____76961
                       (fun uu____76967  ->
                          let env' = push_bvs e' bvs  in
                          let uu____76969 =
                            let uu____76976 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____76976  in
                          bind uu____76969
                            (fun uu____76986  ->
                               match uu____76986 with
                               | (ut,uvar_ut) ->
                                   let uu____76995 = set_solution goal ut  in
                                   bind uu____76995
                                     (fun uu____77000  ->
                                        let uu____77001 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                            goal.FStar_Tactics_Types.label
                                           in
                                        replace_cur uu____77001))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____77009  ->
    let uu____77012 = cur_goal ()  in
    bind uu____77012
      (fun goal  ->
         let uu____77018 =
           let uu____77025 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____77025  in
         match uu____77018 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____77034) ->
             let uu____77039 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____77039)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____77052 = cur_goal ()  in
    bind uu____77052
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____77062 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____77062  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____77065  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____77078 = cur_goal ()  in
    bind uu____77078
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____77088 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____77088  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____77091  -> add_goals [g']))
  
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
            let uu____77132 = FStar_Syntax_Subst.compress t  in
            uu____77132.FStar_Syntax_Syntax.n  in
          let uu____77135 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___1922_77142 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___1922_77142.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___1922_77142.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____77135
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____77159 =
                   let uu____77160 = FStar_Syntax_Subst.compress t1  in
                   uu____77160.FStar_Syntax_Syntax.n  in
                 match uu____77159 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____77191 = ff hd1  in
                     bind uu____77191
                       (fun hd2  ->
                          let fa uu____77217 =
                            match uu____77217 with
                            | (a,q) ->
                                let uu____77238 = ff a  in
                                bind uu____77238 (fun a1  -> ret (a1, q))
                             in
                          let uu____77257 = mapM fa args  in
                          bind uu____77257
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____77339 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____77339 with
                      | (bs1,t') ->
                          let uu____77348 =
                            let uu____77351 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____77351 t'  in
                          bind uu____77348
                            (fun t''  ->
                               let uu____77355 =
                                 let uu____77356 =
                                   let uu____77375 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____77384 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____77375, uu____77384, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____77356  in
                               ret uu____77355))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____77459 = ff hd1  in
                     bind uu____77459
                       (fun hd2  ->
                          let ffb br =
                            let uu____77474 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____77474 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____77506 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____77506  in
                                let uu____77507 = ff1 e  in
                                bind uu____77507
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____77522 = mapM ffb brs  in
                          bind uu____77522
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____77566;
                          FStar_Syntax_Syntax.lbtyp = uu____77567;
                          FStar_Syntax_Syntax.lbeff = uu____77568;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____77570;
                          FStar_Syntax_Syntax.lbpos = uu____77571;_}::[]),e)
                     ->
                     let lb =
                       let uu____77599 =
                         let uu____77600 = FStar_Syntax_Subst.compress t1  in
                         uu____77600.FStar_Syntax_Syntax.n  in
                       match uu____77599 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____77604) -> lb
                       | uu____77620 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____77630 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____77630
                         (fun def1  ->
                            ret
                              (let uu___1875_77636 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1875_77636.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1875_77636.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1875_77636.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1875_77636.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1875_77636.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1875_77636.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____77637 = fflb lb  in
                     bind uu____77637
                       (fun lb1  ->
                          let uu____77647 =
                            let uu____77652 =
                              let uu____77653 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____77653]  in
                            FStar_Syntax_Subst.open_term uu____77652 e  in
                          match uu____77647 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____77683 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____77683  in
                              let uu____77684 = ff1 e1  in
                              bind uu____77684
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____77731 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____77731
                         (fun def  ->
                            ret
                              (let uu___1893_77737 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1893_77737.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1893_77737.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1893_77737.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1893_77737.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1893_77737.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1893_77737.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____77738 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____77738 with
                      | (lbs1,e1) ->
                          let uu____77753 = mapM fflb lbs1  in
                          bind uu____77753
                            (fun lbs2  ->
                               let uu____77765 = ff e1  in
                               bind uu____77765
                                 (fun e2  ->
                                    let uu____77773 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____77773 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____77844 = ff t2  in
                     bind uu____77844
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____77875 = ff t2  in
                     bind uu____77875
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____77882 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___1917_77889 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___1917_77889.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___1917_77889.FStar_Syntax_Syntax.vars)
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
              let uu____77936 =
                FStar_TypeChecker_TcTerm.tc_term
                  (let uu___1930_77945 = env  in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___1930_77945.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___1930_77945.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___1930_77945.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___1930_77945.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_sig =
                       (uu___1930_77945.FStar_TypeChecker_Env.gamma_sig);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___1930_77945.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___1930_77945.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___1930_77945.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___1930_77945.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.attrtab =
                       (uu___1930_77945.FStar_TypeChecker_Env.attrtab);
                     FStar_TypeChecker_Env.is_pattern =
                       (uu___1930_77945.FStar_TypeChecker_Env.is_pattern);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___1930_77945.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___1930_77945.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___1930_77945.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___1930_77945.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___1930_77945.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___1930_77945.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___1930_77945.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___1930_77945.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___1930_77945.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax = true;
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___1930_77945.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.phase1 =
                       (uu___1930_77945.FStar_TypeChecker_Env.phase1);
                     FStar_TypeChecker_Env.failhard =
                       (uu___1930_77945.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___1930_77945.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.uvar_subtyping =
                       (uu___1930_77945.FStar_TypeChecker_Env.uvar_subtyping);
                     FStar_TypeChecker_Env.tc_term =
                       (uu___1930_77945.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.type_of =
                       (uu___1930_77945.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___1930_77945.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.check_type_of =
                       (uu___1930_77945.FStar_TypeChecker_Env.check_type_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___1930_77945.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (uu___1930_77945.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (uu___1930_77945.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.fv_delta_depths =
                       (uu___1930_77945.FStar_TypeChecker_Env.fv_delta_depths);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___1930_77945.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (uu___1930_77945.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.splice =
                       (uu___1930_77945.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.postprocess =
                       (uu___1930_77945.FStar_TypeChecker_Env.postprocess);
                     FStar_TypeChecker_Env.is_native_tactic =
                       (uu___1930_77945.FStar_TypeChecker_Env.is_native_tactic);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___1930_77945.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (uu___1930_77945.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (uu___1930_77945.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.nbe =
                       (uu___1930_77945.FStar_TypeChecker_Env.nbe)
                   }) t
                 in
              match uu____77936 with
              | (t1,lcomp,g) ->
                  let uu____77952 =
                    (let uu____77956 =
                       FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                     Prims.op_Negation uu____77956) ||
                      (let uu____77959 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____77959)
                     in
                  if uu____77952
                  then ret t1
                  else
                    (let rewrite_eq =
                       let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                       let uu____77970 = new_uvar "pointwise_rec" env typ  in
                       bind uu____77970
                         (fun uu____77987  ->
                            match uu____77987 with
                            | (ut,uvar_ut) ->
                                (log ps
                                   (fun uu____78000  ->
                                      let uu____78001 =
                                        FStar_Syntax_Print.term_to_string t1
                                         in
                                      let uu____78003 =
                                        FStar_Syntax_Print.term_to_string ut
                                         in
                                      FStar_Util.print2
                                        "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                        uu____78001 uu____78003);
                                 (let uu____78006 =
                                    let uu____78009 =
                                      let uu____78010 =
                                        FStar_TypeChecker_TcTerm.universe_of
                                          env typ
                                         in
                                      FStar_Syntax_Util.mk_eq2 uu____78010
                                        typ t1 ut
                                       in
                                    add_irrelevant_goal
                                      "pointwise_rec equation" env
                                      uu____78009 opts label1
                                     in
                                  bind uu____78006
                                    (fun uu____78014  ->
                                       let uu____78015 =
                                         bind tau
                                           (fun uu____78021  ->
                                              let ut1 =
                                                FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                  env ut
                                                 in
                                              log ps
                                                (fun uu____78027  ->
                                                   let uu____78028 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1
                                                      in
                                                   let uu____78030 =
                                                     FStar_Syntax_Print.term_to_string
                                                       ut1
                                                      in
                                                   FStar_Util.print2
                                                     "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                     uu____78028 uu____78030);
                                              ret ut1)
                                          in
                                       focus uu____78015))))
                        in
                     let uu____78033 = catch rewrite_eq  in
                     bind uu____78033
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
          let uu____78251 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____78251
            (fun t1  ->
               let uu____78259 =
                 f env
                   (let uu___2007_78268 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___2007_78268.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___2007_78268.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____78259
                 (fun uu____78284  ->
                    match uu____78284 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____78307 =
                               let uu____78308 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____78308.FStar_Syntax_Syntax.n  in
                             match uu____78307 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____78345 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____78345
                                   (fun uu____78370  ->
                                      match uu____78370 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____78386 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____78386
                                            (fun uu____78413  ->
                                               match uu____78413 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___1987_78443 =
                                                         t3  in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___1987_78443.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___1987_78443.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____78485 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____78485 with
                                  | (bs1,t') ->
                                      let uu____78500 =
                                        let uu____78507 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____78507 ctrl1 t'
                                         in
                                      bind uu____78500
                                        (fun uu____78525  ->
                                           match uu____78525 with
                                           | (t'',ctrl2) ->
                                               let uu____78540 =
                                                 let uu____78547 =
                                                   let uu___2000_78550 = t4
                                                      in
                                                   let uu____78553 =
                                                     let uu____78554 =
                                                       let uu____78573 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____78582 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____78573,
                                                         uu____78582, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____78554
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____78553;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___2000_78550.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___2000_78550.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____78547, ctrl2)  in
                                               ret uu____78540))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____78635 -> ret (t3, ctrl1))))

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
              let uu____78682 = ctrl_tac_fold f env ctrl t  in
              bind uu____78682
                (fun uu____78706  ->
                   match uu____78706 with
                   | (t1,ctrl1) ->
                       let uu____78721 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____78721
                         (fun uu____78748  ->
                            match uu____78748 with
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
                let uu____78842 =
                  let uu____78850 =
                    add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                      opts label1
                     in
                  bind uu____78850
                    (fun uu____78861  ->
                       let uu____78862 = ctrl t1  in
                       bind uu____78862
                         (fun res  ->
                            let uu____78889 = trivial ()  in
                            bind uu____78889 (fun uu____78898  -> ret res)))
                   in
                bind uu____78842
                  (fun uu____78916  ->
                     match uu____78916 with
                     | (should_rewrite,ctrl1) ->
                         if Prims.op_Negation should_rewrite
                         then ret (t1, ctrl1)
                         else
                           (let uu____78945 =
                              FStar_TypeChecker_TcTerm.tc_term
                                (let uu___2037_78954 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___2037_78954.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___2037_78954.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___2037_78954.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___2037_78954.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___2037_78954.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___2037_78954.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___2037_78954.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___2037_78954.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___2037_78954.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___2037_78954.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___2037_78954.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___2037_78954.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___2037_78954.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___2037_78954.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___2037_78954.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___2037_78954.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___2037_78954.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___2037_78954.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___2037_78954.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___2037_78954.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___2037_78954.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___2037_78954.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___2037_78954.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___2037_78954.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___2037_78954.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___2037_78954.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___2037_78954.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___2037_78954.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___2037_78954.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___2037_78954.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___2037_78954.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___2037_78954.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___2037_78954.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___2037_78954.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___2037_78954.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___2037_78954.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___2037_78954.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___2037_78954.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___2037_78954.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___2037_78954.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___2037_78954.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___2037_78954.FStar_TypeChecker_Env.nbe)
                                 }) t1
                               in
                            match uu____78945 with
                            | (t2,lcomp,g) ->
                                let uu____78965 =
                                  (let uu____78969 =
                                     FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                       lcomp
                                      in
                                   Prims.op_Negation uu____78969) ||
                                    (let uu____78972 =
                                       FStar_TypeChecker_Env.is_trivial g  in
                                     Prims.op_Negation uu____78972)
                                   in
                                if uu____78965
                                then ret (t2, globalStop)
                                else
                                  (let typ =
                                     lcomp.FStar_Syntax_Syntax.res_typ  in
                                   let uu____78988 =
                                     new_uvar "pointwise_rec" env typ  in
                                   bind uu____78988
                                     (fun uu____79009  ->
                                        match uu____79009 with
                                        | (ut,uvar_ut) ->
                                            (log ps
                                               (fun uu____79026  ->
                                                  let uu____79027 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t2
                                                     in
                                                  let uu____79029 =
                                                    FStar_Syntax_Print.term_to_string
                                                      ut
                                                     in
                                                  FStar_Util.print2
                                                    "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                    uu____79027 uu____79029);
                                             (let uu____79032 =
                                                let uu____79035 =
                                                  let uu____79036 =
                                                    FStar_TypeChecker_TcTerm.universe_of
                                                      env typ
                                                     in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____79036 typ t2 ut
                                                   in
                                                add_irrelevant_goal
                                                  "rewrite_rec equation" env
                                                  uu____79035 opts label1
                                                 in
                                              bind uu____79032
                                                (fun uu____79044  ->
                                                   let uu____79045 =
                                                     bind rewriter
                                                       (fun uu____79059  ->
                                                          let ut1 =
                                                            FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                              env ut
                                                             in
                                                          log ps
                                                            (fun uu____79065 
                                                               ->
                                                               let uu____79066
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   t2
                                                                  in
                                                               let uu____79068
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   ut1
                                                                  in
                                                               FStar_Util.print2
                                                                 "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                                 uu____79066
                                                                 uu____79068);
                                                          ret (ut1, ctrl1))
                                                      in
                                                   focus uu____79045)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term -> (Prims.bool * FStar_BigInt.t) tac) ->
    unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____79114 =
        bind get
          (fun ps  ->
             let uu____79124 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____79124 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____79162  ->
                       let uu____79163 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____79163);
                  bind dismiss_all
                    (fun uu____79168  ->
                       let uu____79169 =
                         let uu____79176 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____79176
                           keepGoing gt1
                          in
                       bind uu____79169
                         (fun uu____79188  ->
                            match uu____79188 with
                            | (gt',uu____79196) ->
                                (log ps
                                   (fun uu____79200  ->
                                      let uu____79201 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____79201);
                                 (let uu____79204 = push_goals gs  in
                                  bind uu____79204
                                    (fun uu____79209  ->
                                       let uu____79210 =
                                         let uu____79213 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____79213]  in
                                       add_goals uu____79210)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____79114
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____79238 =
        bind get
          (fun ps  ->
             let uu____79248 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____79248 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____79286  ->
                       let uu____79287 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____79287);
                  bind dismiss_all
                    (fun uu____79292  ->
                       let uu____79293 =
                         let uu____79296 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____79296 gt1
                          in
                       bind uu____79293
                         (fun gt'  ->
                            log ps
                              (fun uu____79304  ->
                                 let uu____79305 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____79305);
                            (let uu____79308 = push_goals gs  in
                             bind uu____79308
                               (fun uu____79313  ->
                                  let uu____79314 =
                                    let uu____79317 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____79317]  in
                                  add_goals uu____79314))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____79238
  
let (trefl : unit -> unit tac) =
  fun uu____79330  ->
    let uu____79333 =
      let uu____79336 = cur_goal ()  in
      bind uu____79336
        (fun g  ->
           let uu____79354 =
             let uu____79359 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____79359  in
           match uu____79354 with
           | FStar_Pervasives_Native.Some t ->
               let uu____79367 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____79367 with
                | (hd1,args) ->
                    let uu____79406 =
                      let uu____79419 =
                        let uu____79420 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____79420.FStar_Syntax_Syntax.n  in
                      (uu____79419, args)  in
                    (match uu____79406 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____79434::(l,uu____79436)::(r,uu____79438)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____79485 =
                           let uu____79489 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____79489 l r  in
                         bind uu____79485
                           (fun b  ->
                              if b
                              then solve' g FStar_Syntax_Util.exp_unit
                              else
                                (let l1 =
                                   let uu____79500 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____79500 l
                                    in
                                 let r1 =
                                   let uu____79502 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____79502 r
                                    in
                                 let uu____79503 =
                                   let uu____79507 =
                                     FStar_Tactics_Types.goal_env g  in
                                   do_unify uu____79507 l1 r1  in
                                 bind uu____79503
                                   (fun b1  ->
                                      if b1
                                      then
                                        solve' g FStar_Syntax_Util.exp_unit
                                      else
                                        (let uu____79517 =
                                           let uu____79519 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____79519 l1  in
                                         let uu____79520 =
                                           let uu____79522 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____79522 r1  in
                                         fail2
                                           "not a trivial equality ((%s) vs (%s))"
                                           uu____79517 uu____79520))))
                     | (hd2,uu____79525) ->
                         let uu____79542 =
                           let uu____79544 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____79544 t  in
                         fail1 "trefl: not an equality (%s)" uu____79542))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____79333
  
let (dup : unit -> unit tac) =
  fun uu____79561  ->
    let uu____79564 = cur_goal ()  in
    bind uu____79564
      (fun g  ->
         let uu____79570 =
           let uu____79577 = FStar_Tactics_Types.goal_env g  in
           let uu____79578 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____79577 uu____79578  in
         bind uu____79570
           (fun uu____79588  ->
              match uu____79588 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___2129_79598 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___2129_79598.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___2129_79598.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___2129_79598.FStar_Tactics_Types.is_guard);
                      FStar_Tactics_Types.label =
                        (uu___2129_79598.FStar_Tactics_Types.label)
                    }  in
                  bind __dismiss
                    (fun uu____79601  ->
                       let uu____79602 =
                         let uu____79605 = FStar_Tactics_Types.goal_env g  in
                         let uu____79606 =
                           let uu____79607 =
                             let uu____79608 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____79609 =
                               FStar_Tactics_Types.goal_type g  in
                             FStar_TypeChecker_TcTerm.universe_of uu____79608
                               uu____79609
                              in
                           let uu____79610 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____79611 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____79607 uu____79610 u
                             uu____79611
                            in
                         add_irrelevant_goal "dup equation" uu____79605
                           uu____79606 g.FStar_Tactics_Types.opts
                           g.FStar_Tactics_Types.label
                          in
                       bind uu____79602
                         (fun uu____79615  ->
                            let uu____79616 = add_goals [g']  in
                            bind uu____79616 (fun uu____79620  -> ret ())))))
  
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
              let uu____79746 = f x y  in
              if uu____79746 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____79769 -> (acc, l11, l21)  in
        let uu____79784 = aux [] l1 l2  in
        match uu____79784 with | (pr,t1,t2) -> ((FStar_List.rev pr), t1, t2)
  
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
      let uu____79890 = get_phi g1  in
      match uu____79890 with
      | FStar_Pervasives_Native.None  -> fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____79897 = get_phi g2  in
          (match uu____79897 with
           | FStar_Pervasives_Native.None  -> fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let uu____79910 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2)
                  in
               (match uu____79910 with
                | (gamma,r1,r2) ->
                    let t1 =
                      let uu____79941 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1)
                         in
                      close_forall_no_univs1 uu____79941 phi1  in
                    let t2 =
                      let uu____79951 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2)
                         in
                      close_forall_no_univs1 uu____79951 phi2  in
                    let uu____79960 =
                      set_solution g1 FStar_Syntax_Util.exp_unit  in
                    bind uu____79960
                      (fun uu____79965  ->
                         let uu____79966 =
                           set_solution g2 FStar_Syntax_Util.exp_unit  in
                         bind uu____79966
                           (fun uu____79973  ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2  in
                              let nenv =
                                let uu___2180_79978 =
                                  FStar_Tactics_Types.goal_env g1  in
                                let uu____79979 =
                                  FStar_Util.smap_create
                                    (Prims.parse_int "100")
                                   in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___2180_79978.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___2180_79978.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___2180_79978.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___2180_79978.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____79979;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___2180_79978.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___2180_79978.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___2180_79978.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___2180_79978.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___2180_79978.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___2180_79978.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___2180_79978.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___2180_79978.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___2180_79978.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___2180_79978.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___2180_79978.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___2180_79978.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___2180_79978.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___2180_79978.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___2180_79978.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___2180_79978.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___2180_79978.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___2180_79978.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___2180_79978.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___2180_79978.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___2180_79978.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___2180_79978.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___2180_79978.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___2180_79978.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___2180_79978.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___2180_79978.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___2180_79978.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___2180_79978.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___2180_79978.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___2180_79978.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___2180_79978.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___2180_79978.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___2180_79978.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___2180_79978.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___2180_79978.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___2180_79978.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___2180_79978.FStar_TypeChecker_Env.nbe)
                                }  in
                              let uu____79983 =
                                mk_irrelevant_goal "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                  g1.FStar_Tactics_Types.label
                                 in
                              bind uu____79983
                                (fun goal  ->
                                   mlog
                                     (fun uu____79993  ->
                                        let uu____79994 =
                                          goal_to_string_verbose g1  in
                                        let uu____79996 =
                                          goal_to_string_verbose g2  in
                                        let uu____79998 =
                                          goal_to_string_verbose goal  in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____79994 uu____79996 uu____79998)
                                     (fun uu____80002  -> ret goal))))))
  
let (join : unit -> unit tac) =
  fun uu____80010  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____80026 =
               set
                 (let uu___2195_80031 = ps  in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___2195_80031.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.main_goal =
                      (uu___2195_80031.FStar_Tactics_Types.main_goal);
                    FStar_Tactics_Types.all_implicits =
                      (uu___2195_80031.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___2195_80031.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___2195_80031.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___2195_80031.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___2195_80031.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___2195_80031.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___2195_80031.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___2195_80031.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___2195_80031.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___2195_80031.FStar_Tactics_Types.local_state)
                  })
                in
             bind uu____80026
               (fun uu____80034  ->
                  let uu____80035 = join_goals g1 g2  in
                  bind uu____80035 (fun g12  -> add_goals [g12]))
         | uu____80040 -> fail "join: less than 2 goals")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) tac)
  =
  fun t  ->
    let uu____80062 =
      let uu____80069 = cur_goal ()  in
      bind uu____80069
        (fun g  ->
           let uu____80079 =
             let uu____80088 = FStar_Tactics_Types.goal_env g  in
             __tc uu____80088 t  in
           bind uu____80079
             (fun uu____80116  ->
                match uu____80116 with
                | (t1,typ,guard) ->
                    let uu____80132 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____80132 with
                     | (hd1,args) ->
                         let uu____80181 =
                           let uu____80196 =
                             let uu____80197 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____80197.FStar_Syntax_Syntax.n  in
                           (uu____80196, args)  in
                         (match uu____80181 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____80218)::(q,uu____80220)::[]) when
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
                                let uu____80274 =
                                  let uu____80275 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____80275
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____80274
                                 in
                              let g2 =
                                let uu____80277 =
                                  let uu____80278 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____80278
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____80277
                                 in
                              bind __dismiss
                                (fun uu____80285  ->
                                   let uu____80286 = add_goals [g1; g2]  in
                                   bind uu____80286
                                     (fun uu____80295  ->
                                        let uu____80296 =
                                          let uu____80301 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____80302 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____80301, uu____80302)  in
                                        ret uu____80296))
                          | uu____80307 ->
                              let uu____80322 =
                                let uu____80324 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____80324 typ  in
                              fail1 "Not a disjunction: %s" uu____80322))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____80062
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____80359 =
      let uu____80362 = cur_goal ()  in
      bind uu____80362
        (fun g  ->
           FStar_Options.push ();
           (let uu____80375 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____80375);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___2232_80382 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___2232_80382.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___2232_80382.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___2232_80382.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___2232_80382.FStar_Tactics_Types.label)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____80359
  
let (top_env : unit -> env tac) =
  fun uu____80399  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____80414  ->
    let uu____80418 = cur_goal ()  in
    bind uu____80418
      (fun g  ->
         let uu____80425 =
           (FStar_Options.lax ()) ||
             (let uu____80428 = FStar_Tactics_Types.goal_env g  in
              uu____80428.FStar_TypeChecker_Env.lax)
            in
         ret uu____80425)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____80445 =
        mlog
          (fun uu____80450  ->
             let uu____80451 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____80451)
          (fun uu____80456  ->
             let uu____80457 = cur_goal ()  in
             bind uu____80457
               (fun goal  ->
                  let env =
                    let uu____80465 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____80465 ty  in
                  let uu____80466 = __tc_ghost env tm  in
                  bind uu____80466
                    (fun uu____80485  ->
                       match uu____80485 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____80499  ->
                                let uu____80500 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____80500)
                             (fun uu____80504  ->
                                mlog
                                  (fun uu____80507  ->
                                     let uu____80508 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____80508)
                                  (fun uu____80513  ->
                                     let uu____80514 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____80514
                                       (fun uu____80519  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____80445
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____80544 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____80550 =
              let uu____80557 =
                let uu____80558 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____80558
                 in
              new_uvar "uvar_env.2" env uu____80557  in
            bind uu____80550
              (fun uu____80575  ->
                 match uu____80575 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____80544
        (fun typ  ->
           let uu____80587 = new_uvar "uvar_env" env typ  in
           bind uu____80587
             (fun uu____80602  ->
                match uu____80602 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____80621 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____80640 -> g.FStar_Tactics_Types.opts
             | uu____80643 -> FStar_Options.peek ()  in
           let uu____80646 = FStar_Syntax_Util.head_and_args t  in
           match uu____80646 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____80666);
                FStar_Syntax_Syntax.pos = uu____80667;
                FStar_Syntax_Syntax.vars = uu____80668;_},uu____80669)
               ->
               let env1 =
                 let uu___2286_80711 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___2286_80711.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___2286_80711.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___2286_80711.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___2286_80711.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___2286_80711.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___2286_80711.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___2286_80711.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___2286_80711.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___2286_80711.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___2286_80711.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___2286_80711.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___2286_80711.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___2286_80711.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___2286_80711.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___2286_80711.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___2286_80711.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___2286_80711.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___2286_80711.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___2286_80711.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___2286_80711.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___2286_80711.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___2286_80711.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___2286_80711.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___2286_80711.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___2286_80711.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___2286_80711.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___2286_80711.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___2286_80711.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___2286_80711.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___2286_80711.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___2286_80711.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___2286_80711.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___2286_80711.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___2286_80711.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___2286_80711.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___2286_80711.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___2286_80711.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___2286_80711.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___2286_80711.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___2286_80711.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___2286_80711.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___2286_80711.FStar_TypeChecker_Env.nbe)
                 }  in
               let g =
                 FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false ""  in
               let uu____80715 =
                 let uu____80718 = bnorm_goal g  in [uu____80718]  in
               add_goals uu____80715
           | uu____80719 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____80621
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____80781 = if b then t2 else ret false  in
             bind uu____80781 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____80807 = trytac comp  in
      bind uu____80807
        (fun uu___613_80819  ->
           match uu___613_80819 with
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
        let uu____80861 =
          bind get
            (fun ps  ->
               let uu____80869 = __tc e t1  in
               bind uu____80869
                 (fun uu____80890  ->
                    match uu____80890 with
                    | (t11,ty1,g1) ->
                        let uu____80903 = __tc e t2  in
                        bind uu____80903
                          (fun uu____80924  ->
                             match uu____80924 with
                             | (t21,ty2,g2) ->
                                 let uu____80937 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____80937
                                   (fun uu____80944  ->
                                      let uu____80945 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____80945
                                        (fun uu____80953  ->
                                           let uu____80954 =
                                             do_unify e ty1 ty2  in
                                           let uu____80958 =
                                             do_unify e t11 t21  in
                                           tac_and uu____80954 uu____80958)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____80861
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____81006  ->
             let uu____81007 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____81007
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
        (fun uu____81041  ->
           let uu____81042 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____81042)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____81053 =
      mlog
        (fun uu____81058  ->
           let uu____81059 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____81059)
        (fun uu____81064  ->
           let uu____81065 = cur_goal ()  in
           bind uu____81065
             (fun g  ->
                let uu____81071 =
                  let uu____81080 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____81080 ty  in
                bind uu____81071
                  (fun uu____81092  ->
                     match uu____81092 with
                     | (ty1,uu____81102,guard) ->
                         let uu____81104 =
                           let uu____81107 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____81107 guard  in
                         bind uu____81104
                           (fun uu____81111  ->
                              let uu____81112 =
                                let uu____81116 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____81117 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____81116 uu____81117 ty1  in
                              bind uu____81112
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____81126 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____81126
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops]  in
                                      let ng =
                                        let uu____81133 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____81134 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____81133
                                          uu____81134
                                         in
                                      let nty =
                                        let uu____81136 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____81136 ty1  in
                                      let uu____81137 =
                                        let uu____81141 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____81141 ng nty  in
                                      bind uu____81137
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____81150 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____81150
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____81053
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) Prims.list tac)
  =
  fun s_tm  ->
    let uu____81224 =
      let uu____81233 = cur_goal ()  in
      bind uu____81233
        (fun g  ->
           let uu____81245 =
             let uu____81254 = FStar_Tactics_Types.goal_env g  in
             __tc uu____81254 s_tm  in
           bind uu____81245
             (fun uu____81272  ->
                match uu____81272 with
                | (s_tm1,s_ty,guard) ->
                    let uu____81290 =
                      let uu____81293 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____81293 guard  in
                    bind uu____81290
                      (fun uu____81306  ->
                         let uu____81307 =
                           FStar_Syntax_Util.head_and_args' s_ty  in
                         match uu____81307 with
                         | (h,args) ->
                             let uu____81352 =
                               let uu____81359 =
                                 let uu____81360 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____81360.FStar_Syntax_Syntax.n  in
                               match uu____81359 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____81375;
                                      FStar_Syntax_Syntax.vars = uu____81376;_},us)
                                   -> ret (fv, us)
                               | uu____81386 -> fail "type is not an fv"  in
                             bind uu____81352
                               (fun uu____81407  ->
                                  match uu____81407 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____81423 =
                                        let uu____81426 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____81426 t_lid
                                         in
                                      (match uu____81423 with
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
                                                  (fun uu____81477  ->
                                                     let uu____81478 =
                                                       FStar_Syntax_Subst.open_term
                                                         t_ps t_ty
                                                        in
                                                     match uu____81478 with
                                                     | (t_ps1,t_ty1) ->
                                                         let uu____81493 =
                                                           mapM
                                                             (fun c_lid  ->
                                                                let uu____81521
                                                                  =
                                                                  let uu____81524
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                  FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____81524
                                                                    c_lid
                                                                   in
                                                                match uu____81521
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
                                                                    uu____81598
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
                                                                    let uu____81603
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____81603
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____81626
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____81626
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____81669
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs
                                                                     in
                                                                    (match uu____81669
                                                                    with
                                                                    | 
                                                                    (d_ps,bs1)
                                                                    ->
                                                                    let uu____81742
                                                                    =
                                                                    let uu____81744
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp  in
                                                                    Prims.op_Negation
                                                                    uu____81744
                                                                     in
                                                                    failwhen
                                                                    uu____81742
                                                                    "not total?"
                                                                    (fun
                                                                    uu____81763
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
                                                                    uu___614_81780
                                                                    =
                                                                    match uu___614_81780
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____81784)
                                                                    -> true
                                                                    | 
                                                                    uu____81787
                                                                    -> false
                                                                     in
                                                                    let uu____81791
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____81791
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
                                                                    uu____81925
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
                                                                    uu____81987
                                                                     ->
                                                                    match uu____81987
                                                                    with
                                                                    | 
                                                                    ((bv,uu____82007),
                                                                    (t,uu____82009))
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
                                                                    uu____82079
                                                                     ->
                                                                    match uu____82079
                                                                    with
                                                                    | 
                                                                    ((bv,uu____82106),
                                                                    (t,uu____82108))
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
                                                                    uu____82167
                                                                     ->
                                                                    match uu____82167
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
                                                                    let uu____82222
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___2450_82239
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___2450_82239.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___2450_82239.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___2450_82239.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___2450_82239.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___2450_82239.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___2450_82239.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___2450_82239.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___2450_82239.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___2450_82239.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___2450_82239.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___2450_82239.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___2450_82239.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___2450_82239.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___2450_82239.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___2450_82239.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___2450_82239.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___2450_82239.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___2450_82239.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___2450_82239.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___2450_82239.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___2450_82239.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___2450_82239.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___2450_82239.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___2450_82239.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___2450_82239.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___2450_82239.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___2450_82239.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___2450_82239.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___2450_82239.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___2450_82239.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___2450_82239.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___2450_82239.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___2450_82239.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___2450_82239.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___2450_82239.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___2450_82239.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___2450_82239.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___2450_82239.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___2450_82239.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___2450_82239.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___2450_82239.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___2450_82239.FStar_TypeChecker_Env.nbe)
                                                                    }) s_ty
                                                                    pat  in
                                                                    match uu____82222
                                                                    with
                                                                    | 
                                                                    (uu____82253,uu____82254,uu____82255,pat_t,uu____82257,_guard_pat)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____82264
                                                                    =
                                                                    let uu____82265
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____82265
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____82264
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____82270
                                                                    =
                                                                    let uu____82279
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____82279]
                                                                     in
                                                                    let uu____82298
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____82270
                                                                    uu____82298
                                                                     in
                                                                    let nty =
                                                                    let uu____82304
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____82304
                                                                     in
                                                                    let uu____82307
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____82307
                                                                    (fun
                                                                    uu____82337
                                                                     ->
                                                                    match uu____82337
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
                                                                    let uu____82364
                                                                    =
                                                                    let uu____82375
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____82375]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____82364
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____82411
                                                                    =
                                                                    let uu____82422
                                                                    =
                                                                    let uu____82427
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2)  in
                                                                    (fv1,
                                                                    uu____82427)
                                                                     in
                                                                    (g', br,
                                                                    uu____82422)
                                                                     in
                                                                    ret
                                                                    uu____82411))))))
                                                                    | 
                                                                    uu____82448
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                             c_lids
                                                            in
                                                         bind uu____81493
                                                           (fun goal_brs  ->
                                                              let uu____82498
                                                                =
                                                                FStar_List.unzip3
                                                                  goal_brs
                                                                 in
                                                              match uu____82498
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
                                                                  let uu____82571
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                  bind
                                                                    uu____82571
                                                                    (
                                                                    fun
                                                                    uu____82582
                                                                     ->
                                                                    let uu____82583
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____82583
                                                                    (fun
                                                                    uu____82593
                                                                     ->
                                                                    ret infos))))
                                            | uu____82600 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____81224
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____82649::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____82679 = init xs  in x :: uu____82679
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____82692 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      let t3 = FStar_Syntax_Util.unlazy_emb t2  in
      match t3.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____82701) -> inspect t4
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____82767 = last args  in
          (match uu____82767 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____82797 =
                 let uu____82798 =
                   let uu____82803 =
                     let uu____82804 =
                       let uu____82809 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____82809  in
                     uu____82804 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____82803, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____82798  in
               FStar_All.pipe_left ret uu____82797)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____82822,uu____82823) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
          let uu____82876 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____82876 with
           | (bs1,t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____82918 =
                      let uu____82919 =
                        let uu____82924 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____82924)  in
                      FStar_Reflection_Data.Tv_Abs uu____82919  in
                    FStar_All.pipe_left ret uu____82918))
      | FStar_Syntax_Syntax.Tm_type uu____82927 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____82952 ->
          let uu____82967 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____82967 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____82998 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____82998 with
           | (b',t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____83051 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____83064 =
            let uu____83065 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____83065  in
          FStar_All.pipe_left ret uu____83064
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____83086 =
            let uu____83087 =
              let uu____83092 =
                let uu____83093 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____83093  in
              (uu____83092, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____83087  in
          FStar_All.pipe_left ret uu____83086
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____83133 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____83138 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____83138 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____83191 ->
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
             | FStar_Util.Inr uu____83233 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____83237 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____83237 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____83257 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____83263 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____83318 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____83318
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____83339 =
                  let uu____83346 =
                    FStar_List.map
                      (fun uu____83359  ->
                         match uu____83359 with
                         | (p1,uu____83368) -> inspect_pat p1) ps
                     in
                  (fv, uu____83346)  in
                FStar_Reflection_Data.Pat_Cons uu____83339
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
              (fun uu___615_83464  ->
                 match uu___615_83464 with
                 | (pat,uu____83486,t5) ->
                     let uu____83504 = inspect_pat pat  in (uu____83504, t5))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____83513 ->
          ((let uu____83515 =
              let uu____83521 =
                let uu____83523 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____83525 = FStar_Syntax_Print.term_to_string t3  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____83523 uu____83525
                 in
              (FStar_Errors.Warning_CantInspect, uu____83521)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____83515);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____82692
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____83543 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____83543
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____83547 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____83547
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____83551 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____83551
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____83558 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____83558
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____83583 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____83583
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____83600 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____83600
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____83619 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____83619
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____83623 =
          let uu____83624 =
            let uu____83631 =
              let uu____83632 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____83632  in
            FStar_Syntax_Syntax.mk uu____83631  in
          uu____83624 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____83623
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____83640 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____83640
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____83651 =
          let uu____83652 =
            let uu____83659 =
              let uu____83660 =
                let uu____83674 =
                  let uu____83677 =
                    let uu____83678 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____83678]  in
                  FStar_Syntax_Subst.close uu____83677 t2  in
                ((false, [lb]), uu____83674)  in
              FStar_Syntax_Syntax.Tm_let uu____83660  in
            FStar_Syntax_Syntax.mk uu____83659  in
          uu____83652 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____83651
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____83723 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____83723 with
         | (lbs,body) ->
             let uu____83738 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____83738)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____83775 =
                let uu____83776 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____83776  in
              FStar_All.pipe_left wrap uu____83775
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____83783 =
                let uu____83784 =
                  let uu____83798 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____83816 = pack_pat p1  in
                         (uu____83816, false)) ps
                     in
                  (fv, uu____83798)  in
                FStar_Syntax_Syntax.Pat_cons uu____83784  in
              FStar_All.pipe_left wrap uu____83783
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
            (fun uu___616_83865  ->
               match uu___616_83865 with
               | (pat,t1) ->
                   let uu____83882 = pack_pat pat  in
                   (uu____83882, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____83930 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____83930
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____83958 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____83958
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____84004 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____84004
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____84043 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____84043
  
let (lget :
  FStar_Reflection_Data.typ -> Prims.string -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun k  ->
      let uu____84063 =
        bind get
          (fun ps  ->
             let uu____84069 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____84069 with
             | FStar_Pervasives_Native.None  -> fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
      FStar_All.pipe_left (wrap_err "lget") uu____84063
  
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit tac)
  =
  fun _ty  ->
    fun k  ->
      fun t  ->
        let uu____84103 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___2748_84110 = ps  in
                 let uu____84111 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t
                    in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___2748_84110.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___2748_84110.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___2748_84110.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___2748_84110.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___2748_84110.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___2748_84110.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___2748_84110.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___2748_84110.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___2748_84110.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___2748_84110.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___2748_84110.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___2748_84110.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____84111
                 }  in
               set ps1)
           in
        FStar_All.pipe_left (wrap_err "lset") uu____84103
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal * FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun typ  ->
      let uu____84138 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____84138 with
      | (u,ctx_uvars,g_u) ->
          let uu____84171 = FStar_List.hd ctx_uvars  in
          (match uu____84171 with
           | (ctx_uvar,uu____84185) ->
               let g =
                 let uu____84187 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____84187 false
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
        let uu____84210 = goal_of_goal_ty env typ  in
        match uu____84210 with
        | (g,g_u) ->
            let ps =
              let uu____84222 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "TacVerbose")
                 in
              let uu____84225 = FStar_Util.psmap_empty ()  in
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
                FStar_Tactics_Types.tac_verb_dbg = uu____84222;
                FStar_Tactics_Types.local_state = uu____84225
              }  in
            let uu____84235 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____84235)
  