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
    let uu____68786 =
      let uu____68787 = FStar_Tactics_Types.goal_env g  in
      let uu____68788 = FStar_Tactics_Types.goal_type g  in
      bnorm uu____68787 uu____68788  in
    FStar_Tactics_Types.goal_with_type g uu____68786
  
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
      let uu____68902 = FStar_Options.tactics_failhard ()  in
      if uu____68902
      then run t p
      else
        (try (fun uu___640_68912  -> match () with | () -> run t p) ()
         with
         | FStar_Errors.Err (uu____68921,msg) ->
             FStar_Tactics_Result.Failed
               ((FStar_Tactics_Types.TacticFailure msg), p)
         | FStar_Errors.Error (uu____68925,msg,uu____68927) ->
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
           let uu____69007 = run t1 p  in
           match uu____69007 with
           | FStar_Tactics_Result.Success (a,q) ->
               let uu____69014 = t2 a  in run uu____69014 q
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
    let uu____69037 =
      FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head  in
    match uu____69037 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (check_goal_solved :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun goal  -> get_uvar_solved goal.FStar_Tactics_Types.goal_ctx_uvar 
let (goal_to_string_verbose : FStar_Tactics_Types.goal -> Prims.string) =
  fun g  ->
    let uu____69059 =
      FStar_Syntax_Print.ctx_uvar_to_string
        g.FStar_Tactics_Types.goal_ctx_uvar
       in
    let uu____69061 =
      let uu____69063 = check_goal_solved g  in
      match uu____69063 with
      | FStar_Pervasives_Native.None  -> ""
      | FStar_Pervasives_Native.Some t ->
          let uu____69069 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "\tGOAL ALREADY SOLVED!: %s" uu____69069
       in
    FStar_Util.format2 "%s%s\n" uu____69059 uu____69061
  
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
            let uu____69116 = FStar_Options.print_implicits ()  in
            if uu____69116
            then
              let uu____69120 = FStar_Tactics_Types.goal_env g  in
              let uu____69121 = FStar_Tactics_Types.goal_witness g  in
              tts uu____69120 uu____69121
            else
              (let uu____69124 =
                 get_uvar_solved g.FStar_Tactics_Types.goal_ctx_uvar  in
               match uu____69124 with
               | FStar_Pervasives_Native.None  -> "_"
               | FStar_Pervasives_Native.Some t ->
                   let uu____69130 = FStar_Tactics_Types.goal_env g  in
                   let uu____69131 = FStar_Tactics_Types.goal_witness g  in
                   tts uu____69130 uu____69131)
             in
          let num =
            match maybe_num with
            | FStar_Pervasives_Native.None  -> ""
            | FStar_Pervasives_Native.Some (i,n1) ->
                let uu____69154 = FStar_Util.string_of_int i  in
                let uu____69156 = FStar_Util.string_of_int n1  in
                FStar_Util.format2 " %s/%s" uu____69154 uu____69156
             in
          let maybe_label =
            match g.FStar_Tactics_Types.label with
            | "" -> ""
            | l -> Prims.op_Hat " (" (Prims.op_Hat l ")")  in
          let actual_goal =
            if ps.FStar_Tactics_Types.tac_verb_dbg
            then goal_to_string_verbose g
            else
              (let uu____69174 =
                 FStar_Syntax_Print.binders_to_string ", "
                   (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
                  in
               let uu____69177 =
                 let uu____69179 = FStar_Tactics_Types.goal_env g  in
                 tts uu____69179
                   (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                  in
               FStar_Util.format3 "%s |- %s : %s\n" uu____69174 w uu____69177)
             in
          FStar_Util.format4 "%s%s%s:\n%s\n" kind num maybe_label actual_goal
  
let (tacprint : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      let uu____69206 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____69206
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____69231 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____69231
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____69263 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____69263
  
let (comp_to_typ : FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____69273) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____69283) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (get_phi :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun g  ->
    let uu____69303 =
      let uu____69304 = FStar_Tactics_Types.goal_env g  in
      let uu____69305 = FStar_Tactics_Types.goal_type g  in
      FStar_TypeChecker_Normalize.unfold_whnf uu____69304 uu____69305  in
    FStar_Syntax_Util.un_squash uu____69303
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  -> let uu____69314 = get_phi g  in FStar_Option.isSome uu____69314 
let (print : Prims.string -> unit tac) = fun msg  -> tacprint msg; ret () 
let (debugging : unit -> Prims.bool tac) =
  fun uu____69338  ->
    bind get
      (fun ps  ->
         let uu____69346 =
           FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
             (FStar_Options.Other "Tac")
            in
         ret uu____69346)
  
let (ps_to_string :
  (Prims.string * FStar_Tactics_Types.proofstate) -> Prims.string) =
  fun uu____69361  ->
    match uu____69361 with
    | (msg,ps) ->
        let p_imp imp =
          FStar_Syntax_Print.uvar_to_string
            (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
           in
        let n_active = FStar_List.length ps.FStar_Tactics_Types.goals  in
        let n_smt = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
        let n1 = n_active + n_smt  in
        let uu____69393 =
          let uu____69397 =
            let uu____69401 =
              let uu____69403 =
                FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
              FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____69403
                msg
               in
            let uu____69406 =
              let uu____69410 =
                if
                  ps.FStar_Tactics_Types.entry_range <>
                    FStar_Range.dummyRange
                then
                  let uu____69414 =
                    FStar_Range.string_of_def_range
                      ps.FStar_Tactics_Types.entry_range
                     in
                  FStar_Util.format1 "Location: %s\n" uu____69414
                else ""  in
              let uu____69420 =
                let uu____69424 =
                  let uu____69426 =
                    FStar_TypeChecker_Env.debug
                      ps.FStar_Tactics_Types.main_context
                      (FStar_Options.Other "Imp")
                     in
                  if uu____69426
                  then
                    let uu____69431 =
                      FStar_Common.string_of_list p_imp
                        ps.FStar_Tactics_Types.all_implicits
                       in
                    FStar_Util.format1 "Imps: %s\n" uu____69431
                  else ""  in
                [uu____69424]  in
              uu____69410 :: uu____69420  in
            uu____69401 :: uu____69406  in
          let uu____69441 =
            let uu____69445 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "Goal"
                       (FStar_Pervasives_Native.Some
                          (((Prims.parse_int "1") + i), n1)) ps g)
                ps.FStar_Tactics_Types.goals
               in
            let uu____69465 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "SMT Goal"
                       (FStar_Pervasives_Native.Some
                          ((((Prims.parse_int "1") + n_active) + i), n1)) ps
                       g) ps.FStar_Tactics_Types.smt_goals
               in
            FStar_List.append uu____69445 uu____69465  in
          FStar_List.append uu____69397 uu____69441  in
        FStar_String.concat "" uu____69393
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      let uu____69499 =
        let uu____69500 = FStar_Tactics_Types.goal_env g  in
        FStar_TypeChecker_Env.all_binders uu____69500  in
      let uu____69501 =
        let uu____69506 =
          let uu____69507 = FStar_Tactics_Types.goal_env g  in
          FStar_TypeChecker_Env.dsenv uu____69507  in
        FStar_Syntax_Print.binders_to_json uu____69506  in
      FStar_All.pipe_right uu____69499 uu____69501  in
    let uu____69508 =
      let uu____69516 =
        let uu____69524 =
          let uu____69530 =
            let uu____69531 =
              let uu____69539 =
                let uu____69545 =
                  let uu____69546 =
                    let uu____69548 = FStar_Tactics_Types.goal_env g  in
                    let uu____69549 = FStar_Tactics_Types.goal_witness g  in
                    tts uu____69548 uu____69549  in
                  FStar_Util.JsonStr uu____69546  in
                ("witness", uu____69545)  in
              let uu____69552 =
                let uu____69560 =
                  let uu____69566 =
                    let uu____69567 =
                      let uu____69569 = FStar_Tactics_Types.goal_env g  in
                      let uu____69570 = FStar_Tactics_Types.goal_type g  in
                      tts uu____69569 uu____69570  in
                    FStar_Util.JsonStr uu____69567  in
                  ("type", uu____69566)  in
                [uu____69560;
                ("label", (FStar_Util.JsonStr (g.FStar_Tactics_Types.label)))]
                 in
              uu____69539 :: uu____69552  in
            FStar_Util.JsonAssoc uu____69531  in
          ("goal", uu____69530)  in
        [uu____69524]  in
      ("hyps", g_binders) :: uu____69516  in
    FStar_Util.JsonAssoc uu____69508
  
let (ps_to_json :
  (Prims.string * FStar_Tactics_Types.proofstate) -> FStar_Util.json) =
  fun uu____69624  ->
    match uu____69624 with
    | (msg,ps) ->
        let uu____69634 =
          let uu____69642 =
            let uu____69650 =
              let uu____69658 =
                let uu____69666 =
                  let uu____69672 =
                    let uu____69673 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____69673  in
                  ("goals", uu____69672)  in
                let uu____69678 =
                  let uu____69686 =
                    let uu____69692 =
                      let uu____69693 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____69693  in
                    ("smt-goals", uu____69692)  in
                  [uu____69686]  in
                uu____69666 :: uu____69678  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____69658
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____69650  in
          let uu____69727 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____69743 =
                let uu____69749 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____69749)  in
              [uu____69743]
            else []  in
          FStar_List.append uu____69642 uu____69727  in
        FStar_Util.JsonAssoc uu____69634
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____69789  ->
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
         (let uu____69820 = FStar_Tactics_Types.subst_proof_state subst1 ps
             in
          dump_proofstate uu____69820 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let traise : 'a . Prims.exn -> 'a tac =
  fun e  -> mk_tac (fun ps  -> FStar_Tactics_Result.Failed (e, ps)) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____69893 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____69893
          then dump_proofstate ps (Prims.op_Hat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed
           ((FStar_Tactics_Types.TacticFailure msg), ps))
  
let fail1 : 'Auu____69907 . Prims.string -> Prims.string -> 'Auu____69907 tac
  =
  fun msg  ->
    fun x  -> let uu____69924 = FStar_Util.format1 msg x  in fail uu____69924
  
let fail2 :
  'Auu____69935 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____69935 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        let uu____69959 = FStar_Util.format2 msg x y  in fail uu____69959
  
let fail3 :
  'Auu____69972 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____69972 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____70003 = FStar_Util.format3 msg x y z  in fail uu____70003
  
let fail4 :
  'Auu____70018 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____70018 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____70056 = FStar_Util.format4 msg x y z w  in
            fail uu____70056
  
let catch : 'a . 'a tac -> (Prims.exn,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____70091 = run t ps  in
         match uu____70091 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___802_70115 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___802_70115.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___802_70115.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___802_70115.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___802_70115.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___802_70115.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___802_70115.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___802_70115.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___802_70115.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___802_70115.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___802_70115.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___802_70115.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (uu___802_70115.FStar_Tactics_Types.local_state)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let recover : 'a . 'a tac -> (Prims.exn,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let uu____70154 = run t ps  in
         match uu____70154 with
         | FStar_Tactics_Result.Success (a,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inr a), q)
         | FStar_Tactics_Result.Failed (m,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inl m), q))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____70202 = catch t  in
    bind uu____70202
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____70229 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try
           (fun uu___828_70261  ->
              match () with
              | () -> let uu____70266 = trytac t  in run uu____70266 ps) ()
         with
         | FStar_Errors.Err (uu____70282,msg) ->
             (log ps
                (fun uu____70288  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____70294,msg,uu____70296) ->
             (log ps
                (fun uu____70301  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____70338 = run t ps  in
           match uu____70338 with
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
  fun p  -> mk_tac (fun uu____70362  -> FStar_Tactics_Result.Success ((), p)) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___863_70377 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___863_70377.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___863_70377.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___863_70377.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___863_70377.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___863_70377.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___863_70377.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___863_70377.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___863_70377.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___863_70377.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___863_70377.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___863_70377.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___863_70377.FStar_Tactics_Types.local_state)
            }))
  
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____70401 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____70401
         then
           let uu____70405 = FStar_Syntax_Print.term_to_string t1  in
           let uu____70407 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____70405
             uu____70407
         else ());
        (try
           (fun uu___871_70418  ->
              match () with
              | () ->
                  let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
                  ((let uu____70426 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____70426
                    then
                      let uu____70430 =
                        FStar_Common.string_of_option
                          (FStar_TypeChecker_Rel.guard_to_string env) res
                         in
                      let uu____70432 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____70434 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.print3
                        "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____70430
                        uu____70432 uu____70434
                    else ());
                   (match res with
                    | FStar_Pervasives_Native.None  -> ret false
                    | FStar_Pervasives_Native.Some g ->
                        let uu____70445 =
                          add_implicits g.FStar_TypeChecker_Env.implicits  in
                        bind uu____70445 (fun uu____70450  -> ret true)))) ()
         with
         | FStar_Errors.Err (uu____70460,msg) ->
             mlog
               (fun uu____70466  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____70469  -> ret false)
         | FStar_Errors.Error (uu____70472,msg,r) ->
             mlog
               (fun uu____70480  ->
                  let uu____70481 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____70481) (fun uu____70485  -> ret false))
  
let (compress_implicits : unit tac) =
  bind get
    (fun ps  ->
       let imps = ps.FStar_Tactics_Types.all_implicits  in
       let g =
         let uu___897_70499 = FStar_TypeChecker_Env.trivial_guard  in
         {
           FStar_TypeChecker_Env.guard_f =
             (uu___897_70499.FStar_TypeChecker_Env.guard_f);
           FStar_TypeChecker_Env.deferred =
             (uu___897_70499.FStar_TypeChecker_Env.deferred);
           FStar_TypeChecker_Env.univ_ineqs =
             (uu___897_70499.FStar_TypeChecker_Env.univ_ineqs);
           FStar_TypeChecker_Env.implicits = imps
         }  in
       let g1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g
          in
       let ps' =
         let uu___901_70502 = ps  in
         {
           FStar_Tactics_Types.main_context =
             (uu___901_70502.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___901_70502.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (g1.FStar_TypeChecker_Env.implicits);
           FStar_Tactics_Types.goals =
             (uu___901_70502.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___901_70502.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___901_70502.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___901_70502.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___901_70502.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___901_70502.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___901_70502.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___901_70502.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___901_70502.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___901_70502.FStar_Tactics_Types.local_state)
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
          (fun uu____70529  ->
             (let uu____70531 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____70531
              then
                (FStar_Options.push ();
                 (let uu____70536 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____70540 = __do_unify env t1 t2  in
              bind uu____70540
                (fun r  ->
                   (let uu____70551 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____70551 then FStar_Options.pop () else ());
                   ret r)))
  
let (remove_solved_goals : unit tac) =
  bind get
    (fun ps  ->
       let ps' =
         let uu___916_70565 = ps  in
         let uu____70566 =
           FStar_List.filter
             (fun g  ->
                let uu____70572 = check_goal_solved g  in
                FStar_Option.isNone uu____70572) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___916_70565.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___916_70565.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___916_70565.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____70566;
           FStar_Tactics_Types.smt_goals =
             (uu___916_70565.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___916_70565.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___916_70565.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___916_70565.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___916_70565.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___916_70565.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___916_70565.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___916_70565.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___916_70565.FStar_Tactics_Types.local_state)
         }  in
       set ps')
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____70590 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____70590 with
      | FStar_Pervasives_Native.Some uu____70595 ->
          let uu____70596 =
            let uu____70598 = goal_to_string_verbose goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____70598  in
          fail uu____70596
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____70619 = FStar_Tactics_Types.goal_env goal  in
      let uu____70620 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____70619 solution uu____70620
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____70627 =
         let uu___929_70628 = p  in
         let uu____70629 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___929_70628.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___929_70628.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___929_70628.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____70629;
           FStar_Tactics_Types.smt_goals =
             (uu___929_70628.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___929_70628.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___929_70628.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___929_70628.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___929_70628.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___929_70628.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___929_70628.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___929_70628.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___929_70628.FStar_Tactics_Types.local_state)
         }  in
       set uu____70627)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      mlog
        (fun uu____70651  ->
           let uu____70652 =
             let uu____70654 = FStar_Tactics_Types.goal_witness goal  in
             FStar_Syntax_Print.term_to_string uu____70654  in
           let uu____70655 = FStar_Syntax_Print.term_to_string solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____70652 uu____70655)
        (fun uu____70660  ->
           let uu____70661 = trysolve goal solution  in
           bind uu____70661
             (fun b  ->
                if b
                then bind __dismiss (fun uu____70673  -> remove_solved_goals)
                else
                  (let uu____70676 =
                     let uu____70678 =
                       let uu____70680 = FStar_Tactics_Types.goal_env goal
                          in
                       tts uu____70680 solution  in
                     let uu____70681 =
                       let uu____70683 = FStar_Tactics_Types.goal_env goal
                          in
                       let uu____70684 =
                         FStar_Tactics_Types.goal_witness goal  in
                       tts uu____70683 uu____70684  in
                     let uu____70685 =
                       let uu____70687 = FStar_Tactics_Types.goal_env goal
                          in
                       let uu____70688 = FStar_Tactics_Types.goal_type goal
                          in
                       tts uu____70687 uu____70688  in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____70678 uu____70681 uu____70685
                      in
                   fail uu____70676)))
  
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____70705 = set_solution goal solution  in
      bind uu____70705
        (fun uu____70709  ->
           bind __dismiss (fun uu____70711  -> remove_solved_goals))
  
let (set_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___945_70730 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___945_70730.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___945_70730.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___945_70730.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals = gs;
              FStar_Tactics_Types.smt_goals =
                (uu___945_70730.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___945_70730.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___945_70730.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___945_70730.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___945_70730.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___945_70730.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___945_70730.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___945_70730.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___945_70730.FStar_Tactics_Types.local_state)
            }))
  
let (set_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___949_70749 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___949_70749.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___949_70749.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___949_70749.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___949_70749.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals = gs;
              FStar_Tactics_Types.depth =
                (uu___949_70749.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___949_70749.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___949_70749.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___949_70749.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___949_70749.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___949_70749.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___949_70749.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___949_70749.FStar_Tactics_Types.local_state)
            }))
  
let (dismiss_all : unit tac) = set_goals [] 
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____70776 = FStar_Options.defensive ()  in
    if uu____70776
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____70786 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____70786)
         in
      let b2 =
        b1 &&
          (let uu____70790 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____70790)
         in
      let rec aux b3 e =
        let uu____70805 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____70805 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____70825 =
        (let uu____70829 = aux b2 env  in Prims.op_Negation uu____70829) &&
          (let uu____70832 = FStar_ST.op_Bang nwarn  in
           uu____70832 < (Prims.parse_int "5"))
         in
      (if uu____70825
       then
         ((let uu____70858 =
             let uu____70859 = FStar_Tactics_Types.goal_type g  in
             uu____70859.FStar_Syntax_Syntax.pos  in
           let uu____70862 =
             let uu____70868 =
               let uu____70870 = goal_to_string_verbose g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____70870
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____70868)  in
           FStar_Errors.log_issue uu____70858 uu____70862);
          (let uu____70874 =
             let uu____70876 = FStar_ST.op_Bang nwarn  in
             uu____70876 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____70874))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___971_70945 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___971_70945.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___971_70945.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___971_70945.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___971_70945.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___971_70945.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___971_70945.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___971_70945.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___971_70945.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___971_70945.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___971_70945.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___971_70945.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___971_70945.FStar_Tactics_Types.local_state)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___976_70966 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___976_70966.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___976_70966.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___976_70966.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___976_70966.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___976_70966.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___976_70966.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___976_70966.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___976_70966.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___976_70966.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___976_70966.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___976_70966.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___976_70966.FStar_Tactics_Types.local_state)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___981_70987 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___981_70987.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___981_70987.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___981_70987.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___981_70987.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___981_70987.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___981_70987.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___981_70987.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___981_70987.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___981_70987.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___981_70987.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___981_70987.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___981_70987.FStar_Tactics_Types.local_state)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___986_71008 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___986_71008.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___986_71008.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___986_71008.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___986_71008.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___986_71008.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___986_71008.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___986_71008.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___986_71008.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___986_71008.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___986_71008.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___986_71008.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___986_71008.FStar_Tactics_Types.local_state)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____71020  -> add_goals [g]) 
let (new_uvar :
  Prims.string ->
    env ->
      FStar_Reflection_Data.typ ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar) tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____71051 =
          FStar_TypeChecker_Env.new_implicit_var_aux reason
            typ.FStar_Syntax_Syntax.pos env typ
            FStar_Syntax_Syntax.Allow_untyped FStar_Pervasives_Native.None
           in
        match uu____71051 with
        | (u,ctx_uvar,g_u) ->
            let uu____71089 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____71089
              (fun uu____71098  ->
                 let uu____71099 =
                   let uu____71104 =
                     let uu____71105 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____71105  in
                   (u, uu____71104)  in
                 ret uu____71099)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____71126 = FStar_Syntax_Util.un_squash t1  in
    match uu____71126 with
    | FStar_Pervasives_Native.Some t' ->
        let t'1 = FStar_Syntax_Util.unascribe t'  in
        let uu____71138 =
          let uu____71139 = FStar_Syntax_Subst.compress t'1  in
          uu____71139.FStar_Syntax_Syntax.n  in
        (match uu____71138 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____71144 -> false)
    | uu____71146 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____71159 = FStar_Syntax_Util.un_squash t  in
    match uu____71159 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____71170 =
          let uu____71171 = FStar_Syntax_Subst.compress t'  in
          uu____71171.FStar_Syntax_Syntax.n  in
        (match uu____71170 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____71176 -> false)
    | uu____71178 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____71191  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____71203 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____71203 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____71210 = goal_to_string_verbose hd1  in
                    let uu____71212 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____71210 uu____71212);
                   ret hd1)))
  
let (tadmit_t : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____71225 =
      bind get
        (fun ps  ->
           let uu____71231 = cur_goal ()  in
           bind uu____71231
             (fun g  ->
                (let uu____71238 =
                   let uu____71239 = FStar_Tactics_Types.goal_type g  in
                   uu____71239.FStar_Syntax_Syntax.pos  in
                 let uu____71242 =
                   let uu____71248 =
                     let uu____71250 =
                       goal_to_string "" FStar_Pervasives_Native.None ps g
                        in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____71250
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____71248)  in
                 FStar_Errors.log_issue uu____71238 uu____71242);
                solve' g t))
       in
    FStar_All.pipe_left (wrap_err "tadmit_t") uu____71225
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____71273  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___1031_71284 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___1031_71284.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___1031_71284.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___1031_71284.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___1031_71284.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___1031_71284.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___1031_71284.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___1031_71284.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___1031_71284.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___1031_71284.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___1031_71284.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___1031_71284.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (uu___1031_71284.FStar_Tactics_Types.local_state)
           }  in
         let uu____71286 = set ps1  in
         bind uu____71286
           (fun uu____71291  ->
              let uu____71292 = FStar_BigInt.of_int_fs n1  in ret uu____71292))
  
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
              let uu____71330 = env.FStar_TypeChecker_Env.universe_of env phi
                 in
              FStar_Syntax_Util.mk_squash uu____71330 phi  in
            let uu____71331 = new_uvar reason env typ  in
            bind uu____71331
              (fun uu____71346  ->
                 match uu____71346 with
                 | (uu____71353,ctx_uvar) ->
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
             (fun uu____71400  ->
                let uu____71401 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____71401)
             (fun uu____71406  ->
                let e1 =
                  let uu___1049_71408 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1049_71408.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1049_71408.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1049_71408.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1049_71408.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1049_71408.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1049_71408.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1049_71408.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1049_71408.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1049_71408.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1049_71408.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1049_71408.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1049_71408.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1049_71408.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1049_71408.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1049_71408.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1049_71408.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1049_71408.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1049_71408.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1049_71408.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1049_71408.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1049_71408.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1049_71408.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1049_71408.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1049_71408.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1049_71408.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1049_71408.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1049_71408.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1049_71408.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1049_71408.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1049_71408.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1049_71408.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1049_71408.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1049_71408.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1049_71408.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1049_71408.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1049_71408.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1049_71408.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1049_71408.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1049_71408.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1049_71408.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1049_71408.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1049_71408.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___1053_71420  ->
                     match () with
                     | () ->
                         let uu____71429 =
                           FStar_TypeChecker_TcTerm.type_of_tot_term e1 t  in
                         ret uu____71429) ()
                with
                | FStar_Errors.Err (uu____71456,msg) ->
                    let uu____71460 = tts e1 t  in
                    let uu____71462 =
                      let uu____71464 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____71464
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____71460 uu____71462 msg
                | FStar_Errors.Error (uu____71474,msg,uu____71476) ->
                    let uu____71479 = tts e1 t  in
                    let uu____71481 =
                      let uu____71483 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____71483
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____71479 uu____71481 msg))
  
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
             (fun uu____71536  ->
                let uu____71537 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc_ghost(%s)\n" uu____71537)
             (fun uu____71542  ->
                let e1 =
                  let uu___1070_71544 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1070_71544.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1070_71544.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1070_71544.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1070_71544.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1070_71544.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1070_71544.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1070_71544.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1070_71544.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1070_71544.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1070_71544.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1070_71544.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1070_71544.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1070_71544.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1070_71544.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1070_71544.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1070_71544.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1070_71544.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1070_71544.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1070_71544.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1070_71544.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1070_71544.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1070_71544.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1070_71544.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1070_71544.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1070_71544.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1070_71544.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1070_71544.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1070_71544.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1070_71544.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1070_71544.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1070_71544.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1070_71544.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1070_71544.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1070_71544.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1070_71544.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1070_71544.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1070_71544.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1070_71544.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1070_71544.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1070_71544.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1070_71544.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1070_71544.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___1074_71559  ->
                     match () with
                     | () ->
                         let uu____71568 =
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e1 t
                            in
                         (match uu____71568 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____71606,msg) ->
                    let uu____71610 = tts e1 t  in
                    let uu____71612 =
                      let uu____71614 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____71614
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____71610 uu____71612 msg
                | FStar_Errors.Error (uu____71624,msg,uu____71626) ->
                    let uu____71629 = tts e1 t  in
                    let uu____71631 =
                      let uu____71633 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____71633
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____71629 uu____71631 msg))
  
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
             (fun uu____71686  ->
                let uu____71687 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____71687)
             (fun uu____71693  ->
                let e1 =
                  let uu___1095_71695 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1095_71695.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1095_71695.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1095_71695.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1095_71695.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1095_71695.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1095_71695.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1095_71695.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1095_71695.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1095_71695.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1095_71695.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1095_71695.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1095_71695.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1095_71695.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1095_71695.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1095_71695.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1095_71695.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1095_71695.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1095_71695.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1095_71695.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1095_71695.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1095_71695.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1095_71695.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1095_71695.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1095_71695.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1095_71695.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1095_71695.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1095_71695.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1095_71695.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1095_71695.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1095_71695.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1095_71695.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1095_71695.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1095_71695.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1095_71695.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1095_71695.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1095_71695.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1095_71695.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1095_71695.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1095_71695.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1095_71695.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1095_71695.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1095_71695.FStar_TypeChecker_Env.nbe)
                  }  in
                let e2 =
                  let uu___1098_71698 = e1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1098_71698.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1098_71698.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1098_71698.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1098_71698.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1098_71698.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1098_71698.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1098_71698.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1098_71698.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1098_71698.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1098_71698.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1098_71698.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1098_71698.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1098_71698.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1098_71698.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1098_71698.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1098_71698.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1098_71698.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1098_71698.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1098_71698.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1098_71698.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1098_71698.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1098_71698.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1098_71698.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1098_71698.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___1098_71698.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1098_71698.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1098_71698.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1098_71698.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1098_71698.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1098_71698.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1098_71698.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1098_71698.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1098_71698.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1098_71698.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1098_71698.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1098_71698.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1098_71698.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1098_71698.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1098_71698.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1098_71698.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1098_71698.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1098_71698.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___1102_71713  ->
                     match () with
                     | () ->
                         let uu____71722 =
                           FStar_TypeChecker_TcTerm.tc_term e2 t  in
                         (match uu____71722 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____71760,msg) ->
                    let uu____71764 = tts e2 t  in
                    let uu____71766 =
                      let uu____71768 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____71768
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____71764 uu____71766 msg
                | FStar_Errors.Error (uu____71778,msg,uu____71780) ->
                    let uu____71783 = tts e2 t  in
                    let uu____71785 =
                      let uu____71787 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____71787
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____71783 uu____71785 msg))
  
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
  fun uu____71821  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___1127_71840 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___1127_71840.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___1127_71840.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___1127_71840.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___1127_71840.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___1127_71840.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___1127_71840.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___1127_71840.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___1127_71840.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___1127_71840.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___1127_71840.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___1127_71840.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___1127_71840.FStar_Tactics_Types.local_state)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____71865 = get_guard_policy ()  in
      bind uu____71865
        (fun old_pol  ->
           let uu____71871 = set_guard_policy pol  in
           bind uu____71871
             (fun uu____71875  ->
                bind t
                  (fun r  ->
                     let uu____71879 = set_guard_policy old_pol  in
                     bind uu____71879 (fun uu____71883  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____71887 = let uu____71892 = cur_goal ()  in trytac uu____71892  in
  bind uu____71887
    (fun uu___609_71899  ->
       match uu___609_71899 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____71905 = FStar_Options.peek ()  in ret uu____71905)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        mlog
          (fun uu____71930  ->
             let uu____71931 = FStar_TypeChecker_Rel.guard_to_string e g  in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason
               uu____71931)
          (fun uu____71936  ->
             let uu____71937 =
               add_implicits g.FStar_TypeChecker_Env.implicits  in
             bind uu____71937
               (fun uu____71941  ->
                  bind getopts
                    (fun opts  ->
                       let uu____71945 =
                         let uu____71946 =
                           FStar_TypeChecker_Rel.simplify_guard e g  in
                         uu____71946.FStar_TypeChecker_Env.guard_f  in
                       match uu____71945 with
                       | FStar_TypeChecker_Common.Trivial  -> ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____71950 = istrivial e f  in
                           if uu____71950
                           then ret ()
                           else
                             bind get
                               (fun ps  ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop  ->
                                      ((let uu____71963 =
                                          let uu____71969 =
                                            let uu____71971 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g
                                               in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____71971
                                             in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____71969)
                                           in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____71963);
                                       ret ())
                                  | FStar_Tactics_Types.Goal  ->
                                      mlog
                                        (fun uu____71977  ->
                                           let uu____71978 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____71978)
                                        (fun uu____71983  ->
                                           let uu____71984 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____71984
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___1156_71992 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___1156_71992.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___1156_71992.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___1156_71992.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___1156_71992.FStar_Tactics_Types.label)
                                                  }  in
                                                push_goals [goal1]))
                                  | FStar_Tactics_Types.SMT  ->
                                      mlog
                                        (fun uu____71996  ->
                                           let uu____71997 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____71997)
                                        (fun uu____72002  ->
                                           let uu____72003 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____72003
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___1163_72011 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___1163_72011.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___1163_72011.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___1163_72011.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___1163_72011.FStar_Tactics_Types.label)
                                                  }  in
                                                push_smt_goals [goal1]))
                                  | FStar_Tactics_Types.Force  ->
                                      mlog
                                        (fun uu____72015  ->
                                           let uu____72016 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____72016)
                                        (fun uu____72020  ->
                                           try
                                             (fun uu___1170_72025  ->
                                                match () with
                                                | () ->
                                                    let uu____72028 =
                                                      let uu____72030 =
                                                        let uu____72032 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____72032
                                                         in
                                                      Prims.op_Negation
                                                        uu____72030
                                                       in
                                                    if uu____72028
                                                    then
                                                      mlog
                                                        (fun uu____72039  ->
                                                           let uu____72040 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g
                                                              in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____72040)
                                                        (fun uu____72044  ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else ret ()) ()
                                           with
                                           | uu___1169_72049 ->
                                               mlog
                                                 (fun uu____72054  ->
                                                    let uu____72055 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g
                                                       in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____72055)
                                                 (fun uu____72059  ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____72071 =
      let uu____72074 = cur_goal ()  in
      bind uu____72074
        (fun goal  ->
           let uu____72080 =
             let uu____72089 = FStar_Tactics_Types.goal_env goal  in
             __tc_lax uu____72089 t  in
           bind uu____72080
             (fun uu____72100  ->
                match uu____72100 with
                | (uu____72109,typ,uu____72111) -> ret typ))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____72071
  
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
            let uu____72151 = mk_irrelevant_goal reason env phi opts label1
               in
            bind uu____72151 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____72163  ->
    let uu____72166 = cur_goal ()  in
    bind uu____72166
      (fun goal  ->
         let uu____72172 =
           let uu____72174 = FStar_Tactics_Types.goal_env goal  in
           let uu____72175 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____72174 uu____72175  in
         if uu____72172
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____72181 =
              let uu____72183 = FStar_Tactics_Types.goal_env goal  in
              let uu____72184 = FStar_Tactics_Types.goal_type goal  in
              tts uu____72183 uu____72184  in
            fail1 "Not a trivial goal: %s" uu____72181))
  
let divide : 'a 'b . FStar_BigInt.t -> 'a tac -> 'b tac -> ('a * 'b) tac =
  fun n1  ->
    fun l  ->
      fun r  ->
        bind get
          (fun p  ->
             let uu____72235 =
               try
                 (fun uu___1226_72258  ->
                    match () with
                    | () ->
                        let uu____72269 =
                          let uu____72278 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____72278
                            p.FStar_Tactics_Types.goals
                           in
                        ret uu____72269) ()
               with | uu___1225_72289 -> fail "divide: not enough goals"  in
             bind uu____72235
               (fun uu____72326  ->
                  match uu____72326 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___1208_72352 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___1208_72352.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___1208_72352.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___1208_72352.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___1208_72352.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___1208_72352.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___1208_72352.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___1208_72352.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___1208_72352.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___1208_72352.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___1208_72352.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___1208_72352.FStar_Tactics_Types.local_state)
                        }  in
                      let uu____72353 = set lp  in
                      bind uu____72353
                        (fun uu____72361  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___1214_72377 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___1214_72377.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___1214_72377.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___1214_72377.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___1214_72377.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___1214_72377.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___1214_72377.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___1214_72377.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___1214_72377.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___1214_72377.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___1214_72377.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___1214_72377.FStar_Tactics_Types.local_state)
                                       }  in
                                     let uu____72378 = set rp  in
                                     bind uu____72378
                                       (fun uu____72386  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___1220_72402 =
                                                        rp'  in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___1220_72402.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___1220_72402.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___1220_72402.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___1220_72402.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___1220_72402.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___1220_72402.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___1220_72402.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___1220_72402.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___1220_72402.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___1220_72402.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___1220_72402.FStar_Tactics_Types.local_state)
                                                      }  in
                                                    let uu____72403 = set p'
                                                       in
                                                    bind uu____72403
                                                      (fun uu____72411  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____72417 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____72439 = divide FStar_BigInt.one f idtac  in
    bind uu____72439
      (fun uu____72452  -> match uu____72452 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____72490::uu____72491 ->
             let uu____72494 =
               let uu____72503 = map tau  in
               divide FStar_BigInt.one tau uu____72503  in
             bind uu____72494
               (fun uu____72521  ->
                  match uu____72521 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____72563 =
        bind t1
          (fun uu____72568  ->
             let uu____72569 = map t2  in
             bind uu____72569 (fun uu____72577  -> ret ()))
         in
      focus uu____72563
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____72587  ->
    let uu____72590 =
      let uu____72593 = cur_goal ()  in
      bind uu____72593
        (fun goal  ->
           let uu____72602 =
             let uu____72609 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____72609  in
           match uu____72602 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____72618 =
                 let uu____72620 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____72620  in
               if uu____72618
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____72629 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____72629 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____72643 = new_uvar "intro" env' typ'  in
                  bind uu____72643
                    (fun uu____72660  ->
                       match uu____72660 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c))
                              in
                           let uu____72684 = set_solution goal sol  in
                           bind uu____72684
                             (fun uu____72690  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                    goal.FStar_Tactics_Types.label
                                   in
                                let uu____72692 =
                                  let uu____72695 = bnorm_goal g  in
                                  replace_cur uu____72695  in
                                bind uu____72692 (fun uu____72697  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____72702 =
                 let uu____72704 = FStar_Tactics_Types.goal_env goal  in
                 let uu____72705 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____72704 uu____72705  in
               fail1 "goal is not an arrow (%s)" uu____72702)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____72590
  
let (intro_rec :
  unit -> (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder) tac) =
  fun uu____72723  ->
    let uu____72730 = cur_goal ()  in
    bind uu____72730
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____72749 =
            let uu____72756 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____72756  in
          match uu____72749 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____72769 =
                let uu____72771 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____72771  in
              if uu____72769
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____72788 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____72788
                    in
                 let bs =
                   let uu____72799 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____72799; b]  in
                 let env' =
                   let uu____72825 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____72825 bs  in
                 let uu____72826 =
                   let uu____72833 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____72833  in
                 bind uu____72826
                   (fun uu____72853  ->
                      match uu____72853 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____72867 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____72870 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____72867
                              FStar_Parser_Const.effect_Tot_lid uu____72870
                              [] FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____72888 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____72888 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____72910 =
                                   let uu____72911 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____72911.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____72910
                                  in
                               let uu____72927 = set_solution goal tm  in
                               bind uu____72927
                                 (fun uu____72936  ->
                                    let uu____72937 =
                                      let uu____72940 =
                                        bnorm_goal
                                          (let uu___1291_72943 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___1291_72943.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___1291_72943.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___1291_72943.FStar_Tactics_Types.is_guard);
                                             FStar_Tactics_Types.label =
                                               (uu___1291_72943.FStar_Tactics_Types.label)
                                           })
                                         in
                                      replace_cur uu____72940  in
                                    bind uu____72937
                                      (fun uu____72950  ->
                                         let uu____72951 =
                                           let uu____72956 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____72956, b)  in
                                         ret uu____72951)))))
          | FStar_Pervasives_Native.None  ->
              let uu____72965 =
                let uu____72967 = FStar_Tactics_Types.goal_env goal  in
                let uu____72968 = FStar_Tactics_Types.goal_type goal  in
                tts uu____72967 uu____72968  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____72965))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____72988 = cur_goal ()  in
    bind uu____72988
      (fun goal  ->
         mlog
           (fun uu____72995  ->
              let uu____72996 =
                let uu____72998 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____72998  in
              FStar_Util.print1 "norm: witness = %s\n" uu____72996)
           (fun uu____73004  ->
              let steps =
                let uu____73008 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____73008
                 in
              let t =
                let uu____73012 = FStar_Tactics_Types.goal_env goal  in
                let uu____73013 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____73012 uu____73013  in
              let uu____73014 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____73014))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____73039 =
          bind get
            (fun ps  ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
                 | g::uu____73047 -> g.FStar_Tactics_Types.opts
                 | uu____73050 -> FStar_Options.peek ()  in
               mlog
                 (fun uu____73055  ->
                    let uu____73056 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____73056)
                 (fun uu____73061  ->
                    let uu____73062 = __tc_lax e t  in
                    bind uu____73062
                      (fun uu____73083  ->
                         match uu____73083 with
                         | (t1,uu____73093,uu____73094) ->
                             let steps =
                               let uu____73098 =
                                 FStar_TypeChecker_Normalize.tr_norm_steps s
                                  in
                               FStar_List.append
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu____73098
                                in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1
                                in
                             mlog
                               (fun uu____73104  ->
                                  let uu____73105 =
                                    FStar_Syntax_Print.term_to_string t2  in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____73105)
                               (fun uu____73109  -> ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____73039
  
let (refine_intro : unit -> unit tac) =
  fun uu____73122  ->
    let uu____73125 =
      let uu____73128 = cur_goal ()  in
      bind uu____73128
        (fun g  ->
           let uu____73135 =
             let uu____73146 = FStar_Tactics_Types.goal_env g  in
             let uu____73147 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____73146
               uu____73147
              in
           match uu____73135 with
           | (uu____73150,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____73176 =
                 let uu____73181 =
                   let uu____73186 =
                     let uu____73187 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____73187]  in
                   FStar_Syntax_Subst.open_term uu____73186 phi  in
                 match uu____73181 with
                 | (bvs,phi1) ->
                     let uu____73212 =
                       let uu____73213 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____73213  in
                     (uu____73212, phi1)
                  in
               (match uu____73176 with
                | (bv1,phi1) ->
                    let uu____73232 =
                      let uu____73235 = FStar_Tactics_Types.goal_env g  in
                      let uu____73236 =
                        let uu____73237 =
                          let uu____73240 =
                            let uu____73241 =
                              let uu____73248 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____73248)  in
                            FStar_Syntax_Syntax.NT uu____73241  in
                          [uu____73240]  in
                        FStar_Syntax_Subst.subst uu____73237 phi1  in
                      mk_irrelevant_goal "refine_intro refinement"
                        uu____73235 uu____73236 g.FStar_Tactics_Types.opts
                        g.FStar_Tactics_Types.label
                       in
                    bind uu____73232
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____73257  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____73125
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____73280 = cur_goal ()  in
      bind uu____73280
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____73289 = FStar_Tactics_Types.goal_env goal  in
               let uu____73290 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____73289 uu____73290
             else FStar_Tactics_Types.goal_env goal  in
           let uu____73293 = __tc env t  in
           bind uu____73293
             (fun uu____73312  ->
                match uu____73312 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____73327  ->
                         let uu____73328 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____73330 =
                           let uu____73332 =
                             FStar_Tactics_Types.goal_env goal  in
                           FStar_TypeChecker_Rel.guard_to_string uu____73332
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____73328 uu____73330)
                      (fun uu____73336  ->
                         let uu____73337 =
                           let uu____73340 =
                             FStar_Tactics_Types.goal_env goal  in
                           proc_guard "__exact typing" uu____73340 guard  in
                         bind uu____73337
                           (fun uu____73343  ->
                              mlog
                                (fun uu____73347  ->
                                   let uu____73348 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____73350 =
                                     let uu____73352 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____73352
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____73348 uu____73350)
                                (fun uu____73356  ->
                                   let uu____73357 =
                                     let uu____73361 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____73362 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____73361 typ uu____73362  in
                                   bind uu____73357
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____73372 =
                                             let uu____73374 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____73374 t1  in
                                           let uu____73375 =
                                             let uu____73377 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____73377 typ  in
                                           let uu____73378 =
                                             let uu____73380 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____73381 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____73380 uu____73381  in
                                           let uu____73382 =
                                             let uu____73384 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____73385 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____73384 uu____73385  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____73372 uu____73375
                                             uu____73378 uu____73382)))))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun try_refine  ->
    fun set_expected_typ1  ->
      fun tm  ->
        let uu____73411 =
          mlog
            (fun uu____73416  ->
               let uu____73417 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____73417)
            (fun uu____73422  ->
               let uu____73423 =
                 let uu____73430 = __exact_now set_expected_typ1 tm  in
                 catch uu____73430  in
               bind uu____73423
                 (fun uu___611_73439  ->
                    match uu___611_73439 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        traise e
                    | FStar_Util.Inl e ->
                        mlog
                          (fun uu____73450  ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____73454  ->
                             let uu____73455 =
                               let uu____73462 =
                                 let uu____73465 =
                                   norm [FStar_Syntax_Embeddings.Delta]  in
                                 bind uu____73465
                                   (fun uu____73470  ->
                                      let uu____73471 = refine_intro ()  in
                                      bind uu____73471
                                        (fun uu____73475  ->
                                           __exact_now set_expected_typ1 tm))
                                  in
                               catch uu____73462  in
                             bind uu____73455
                               (fun uu___610_73482  ->
                                  match uu___610_73482 with
                                  | FStar_Util.Inr r ->
                                      mlog
                                        (fun uu____73491  ->
                                           FStar_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu____73494  -> ret ())
                                  | FStar_Util.Inl uu____73495 ->
                                      mlog
                                        (fun uu____73497  ->
                                           FStar_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu____73500  -> traise e)))))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____73411
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____73552 = f x  in
          bind uu____73552
            (fun y  ->
               let uu____73560 = mapM f xs  in
               bind uu____73560 (fun ys  -> ret (y :: ys)))
  
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
          let uu____73632 = do_unify e ty1 ty2  in
          bind uu____73632
            (fun uu___612_73646  ->
               if uu___612_73646
               then ret acc
               else
                 (let uu____73666 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____73666 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____73687 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____73689 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____73687
                        uu____73689
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____73706 =
                        let uu____73708 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____73708  in
                      if uu____73706
                      then fail "Codomain is effectful"
                      else
                        (let uu____73732 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____73732
                           (fun uu____73759  ->
                              match uu____73759 with
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
      let uu____73849 =
        mlog
          (fun uu____73854  ->
             let uu____73855 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_apply: tm = %s\n" uu____73855)
          (fun uu____73860  ->
             let uu____73861 = cur_goal ()  in
             bind uu____73861
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____73869 = __tc e tm  in
                  bind uu____73869
                    (fun uu____73890  ->
                       match uu____73890 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____73903 =
                             let uu____73914 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____73914  in
                           bind uu____73903
                             (fun uvs  ->
                                let fix_qual q =
                                  match q with
                                  | FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Meta uu____73952)
                                      ->
                                      FStar_Pervasives_Native.Some
                                        (FStar_Syntax_Syntax.Implicit false)
                                  | uu____73956 -> q  in
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____73979  ->
                                       fun w  ->
                                         match uu____73979 with
                                         | (uvt,q,uu____73997) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, (fix_qual q))]) uvs tm1
                                   in
                                let uvset =
                                  let uu____74029 =
                                    FStar_Syntax_Free.new_uv_set ()  in
                                  FStar_List.fold_right
                                    (fun uu____74046  ->
                                       fun s  ->
                                         match uu____74046 with
                                         | (uu____74058,uu____74059,uv) ->
                                             let uu____74061 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                in
                                             FStar_Util.set_union s
                                               uu____74061) uvs uu____74029
                                   in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset  in
                                let uu____74071 = solve' goal w  in
                                bind uu____74071
                                  (fun uu____74076  ->
                                     let uu____74077 =
                                       mapM
                                         (fun uu____74094  ->
                                            match uu____74094 with
                                            | (uvt,q,uv) ->
                                                let uu____74106 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                   in
                                                (match uu____74106 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____74111 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____74112 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv)
                                                        in
                                                     if uu____74112
                                                     then ret ()
                                                     else
                                                       (let uu____74119 =
                                                          let uu____74122 =
                                                            bnorm_goal
                                                              (let uu___1452_74125
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___1452_74125.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___1452_74125.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false;
                                                                 FStar_Tactics_Types.label
                                                                   =
                                                                   (uu___1452_74125.FStar_Tactics_Types.label)
                                                               })
                                                             in
                                                          [uu____74122]  in
                                                        add_goals uu____74119)))
                                         uvs
                                        in
                                     bind uu____74077
                                       (fun uu____74130  ->
                                          proc_guard "apply guard" e guard))))))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____73849
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____74158 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____74158
    then
      let uu____74167 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____74182 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____74235 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____74167 with
      | (pre,post) ->
          let post1 =
            let uu____74268 =
              let uu____74279 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____74279]  in
            FStar_Syntax_Util.mk_app post uu____74268  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____74310 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____74310
       then
         let uu____74319 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____74319
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
            let uu____74398 = f x e  in
            bind uu____74398 (fun e'  -> fold_left f e' xs1)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____74413 =
      let uu____74416 =
        bind get
          (fun ps  ->
             mlog
               (fun uu____74423  ->
                  let uu____74424 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____74424)
               (fun uu____74430  ->
                  let is_unit_t t =
                    let uu____74438 =
                      let uu____74439 = FStar_Syntax_Subst.compress t  in
                      uu____74439.FStar_Syntax_Syntax.n  in
                    match uu____74438 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____74445 -> false  in
                  let uu____74447 = cur_goal ()  in
                  bind uu____74447
                    (fun goal  ->
                       let uu____74453 =
                         let uu____74462 = FStar_Tactics_Types.goal_env goal
                            in
                         __tc uu____74462 tm  in
                       bind uu____74453
                         (fun uu____74477  ->
                            match uu____74477 with
                            | (tm1,t,guard) ->
                                let uu____74489 =
                                  FStar_Syntax_Util.arrow_formals_comp t  in
                                (match uu____74489 with
                                 | (bs,comp) ->
                                     let uu____74522 = lemma_or_sq comp  in
                                     (match uu____74522 with
                                      | FStar_Pervasives_Native.None  ->
                                          fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre,post) ->
                                          let uu____74542 =
                                            fold_left
                                              (fun uu____74604  ->
                                                 fun uu____74605  ->
                                                   match (uu____74604,
                                                           uu____74605)
                                                   with
                                                   | ((b,aq),(uvs,imps,subst1))
                                                       ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst1
                                                           b.FStar_Syntax_Syntax.sort
                                                          in
                                                       let uu____74756 =
                                                         is_unit_t b_t  in
                                                       if uu____74756
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
                                                         (let uu____74879 =
                                                            let uu____74886 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            new_uvar
                                                              "apply_lemma"
                                                              uu____74886 b_t
                                                             in
                                                          bind uu____74879
                                                            (fun uu____74917 
                                                               ->
                                                               match uu____74917
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
                                          bind uu____74542
                                            (fun uu____75103  ->
                                               match uu____75103 with
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
                                                   let uu____75191 =
                                                     let uu____75195 =
                                                       FStar_Tactics_Types.goal_env
                                                         goal
                                                        in
                                                     let uu____75196 =
                                                       FStar_Syntax_Util.mk_squash
                                                         FStar_Syntax_Syntax.U_zero
                                                         post1
                                                        in
                                                     let uu____75197 =
                                                       FStar_Tactics_Types.goal_type
                                                         goal
                                                        in
                                                     do_unify uu____75195
                                                       uu____75196
                                                       uu____75197
                                                      in
                                                   bind uu____75191
                                                     (fun b  ->
                                                        if
                                                          Prims.op_Negation b
                                                        then
                                                          let uu____75208 =
                                                            let uu____75210 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            tts uu____75210
                                                              tm1
                                                             in
                                                          let uu____75211 =
                                                            let uu____75213 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            let uu____75214 =
                                                              FStar_Syntax_Util.mk_squash
                                                                FStar_Syntax_Syntax.U_zero
                                                                post1
                                                               in
                                                            tts uu____75213
                                                              uu____75214
                                                             in
                                                          let uu____75215 =
                                                            let uu____75217 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            let uu____75218 =
                                                              FStar_Tactics_Types.goal_type
                                                                goal
                                                               in
                                                            tts uu____75217
                                                              uu____75218
                                                             in
                                                          fail3
                                                            "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                            uu____75208
                                                            uu____75211
                                                            uu____75215
                                                        else
                                                          (let uu____75222 =
                                                             solve' goal
                                                               FStar_Syntax_Util.exp_unit
                                                              in
                                                           bind uu____75222
                                                             (fun uu____75230
                                                                 ->
                                                                let is_free_uvar
                                                                  uv t1 =
                                                                  let free_uvars
                                                                    =
                                                                    let uu____75256
                                                                    =
                                                                    let uu____75259
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____75259
                                                                     in
                                                                    FStar_List.map
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____75256
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
                                                                    let uu____75295
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____75295)
                                                                    goals
                                                                   in
                                                                let checkone
                                                                  t1 goals =
                                                                  let uu____75312
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                  match uu____75312
                                                                  with
                                                                  | (hd1,uu____75331)
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____75358)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____75375
                                                                    -> false)
                                                                   in
                                                                let uu____75377
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
                                                                    let uu____75420
                                                                    = imp  in
                                                                    match uu____75420
                                                                    with
                                                                    | 
                                                                    (term,ctx_uvar)
                                                                    ->
                                                                    let uu____75431
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____75431
                                                                    with
                                                                    | 
                                                                    (hd1,uu____75453)
                                                                    ->
                                                                    let uu____75478
                                                                    =
                                                                    let uu____75479
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____75479.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____75478
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____75487)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___1562_75507
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___1562_75507.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___1562_75507.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___1562_75507.FStar_Tactics_Types.is_guard);
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___1562_75507.FStar_Tactics_Types.label)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____75510
                                                                    ->
                                                                    mlog
                                                                    (fun
                                                                    uu____75516
                                                                     ->
                                                                    let uu____75517
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                                                     in
                                                                    let uu____75519
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____75517
                                                                    uu____75519)
                                                                    (fun
                                                                    uu____75526
                                                                     ->
                                                                    let env =
                                                                    let uu___1567_75528
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___1567_75528.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1567_75528.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1567_75528.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___1567_75528.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1567_75528.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1567_75528.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1567_75528.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1567_75528.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___1567_75528.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___1567_75528.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___1567_75528.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1567_75528.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1567_75528.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1567_75528.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1567_75528.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1567_75528.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1567_75528.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1567_75528.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___1567_75528.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___1567_75528.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___1567_75528.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1567_75528.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1567_75528.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1567_75528.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1567_75528.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1567_75528.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1567_75528.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1567_75528.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1567_75528.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1567_75528.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1567_75528.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1567_75528.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1567_75528.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1567_75528.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___1567_75528.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1567_75528.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1567_75528.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___1567_75528.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1567_75528.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1567_75528.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1567_75528.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1567_75528.FStar_TypeChecker_Env.nbe)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let uu____75531
                                                                    =
                                                                    let uu____75534
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____75538
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
                                                                    let uu____75540
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____75538
                                                                    uu____75540
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____75546
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    uu____75534
                                                                    uu____75546
                                                                    g_typ  in
                                                                    bind
                                                                    uu____75531
                                                                    (fun
                                                                    uu____75550
                                                                     ->
                                                                    ret []))))))
                                                                   in
                                                                bind
                                                                  uu____75377
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
                                                                    let uu____75614
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____75614
                                                                    then
                                                                    let uu____75619
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____75619
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
                                                                    let uu____75634
                                                                    =
                                                                    let uu____75636
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____75636
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____75634)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____75637
                                                                    =
                                                                    let uu____75640
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____75640
                                                                    guard  in
                                                                    bind
                                                                    uu____75637
                                                                    (fun
                                                                    uu____75644
                                                                     ->
                                                                    let uu____75645
                                                                    =
                                                                    let uu____75648
                                                                    =
                                                                    let uu____75650
                                                                    =
                                                                    let uu____75652
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____75653
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____75652
                                                                    uu____75653
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____75650
                                                                     in
                                                                    if
                                                                    uu____75648
                                                                    then
                                                                    let uu____75657
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____75657
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    goal.FStar_Tactics_Types.label
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____75645
                                                                    (fun
                                                                    uu____75662
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2)))))))))))))
         in
      focus uu____74416  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____74413
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____75686 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____75686 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____75696::(e1,uu____75698)::(e2,uu____75700)::[])) when
        (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) ||
          (FStar_Ident.lid_equals l FStar_Parser_Const.c_eq2_lid)
        -> FStar_Pervasives_Native.Some (e1, e2)
    | uu____75761 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____75786 = destruct_eq' typ  in
    match uu____75786 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____75816 = FStar_Syntax_Util.un_squash typ  in
        (match uu____75816 with
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
        let uu____75885 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____75885 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', bv', [])
            else
              (let uu____75943 = aux e'  in
               FStar_Util.map_opt uu____75943
                 (fun uu____75974  ->
                    match uu____75974 with
                    | (e'',bv,bvs) -> (e'', bv, (bv' :: bvs))))
         in
      let uu____76000 = aux e  in
      FStar_Util.map_opt uu____76000
        (fun uu____76031  ->
           match uu____76031 with
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
          let uu____76105 =
            let uu____76116 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____76116  in
          FStar_Util.map_opt uu____76105
            (fun uu____76134  ->
               match uu____76134 with
               | (e0,b11,bvs) ->
                   let s1 bv =
                     let uu___1640_76156 = bv  in
                     let uu____76157 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___1640_76156.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___1640_76156.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____76157
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___1644_76165 =
                       g.FStar_Tactics_Types.goal_ctx_uvar  in
                     let uu____76166 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____76175 =
                       let uu____76178 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____76178  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___1644_76165.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____76166;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____76175;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___1644_76165.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___1644_76165.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___1644_76165.FStar_Syntax_Syntax.ctx_uvar_range);
                       FStar_Syntax_Syntax.ctx_uvar_meta =
                         (uu___1644_76165.FStar_Syntax_Syntax.ctx_uvar_meta)
                     }  in
                   let uu___1647_76179 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1647_76179.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___1647_76179.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___1647_76179.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1647_76179.FStar_Tactics_Types.label)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____76190 =
      let uu____76193 = cur_goal ()  in
      bind uu____76193
        (fun goal  ->
           let uu____76201 = h  in
           match uu____76201 with
           | (bv,uu____76205) ->
               mlog
                 (fun uu____76213  ->
                    let uu____76214 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____76216 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____76214
                      uu____76216)
                 (fun uu____76221  ->
                    let uu____76222 =
                      let uu____76233 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____76233  in
                    match uu____76222 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                        let uu____76260 =
                          destruct_eq bv1.FStar_Syntax_Syntax.sort  in
                        (match uu____76260 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____76275 =
                               let uu____76276 =
                                 FStar_Syntax_Subst.compress x  in
                               uu____76276.FStar_Syntax_Syntax.n  in
                             (match uu____76275 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv2 =
                                    let uu___1670_76293 = bv2  in
                                    let uu____76294 =
                                      FStar_Syntax_Subst.subst s
                                        bv2.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1670_76293.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1670_76293.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____76294
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv1 :: bvs1)  in
                                  let new_goal =
                                    let uu___1674_76302 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____76303 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____76312 =
                                      let uu____76315 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____76315
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___1674_76302.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____76303;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____76312;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___1674_76302.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___1674_76302.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___1674_76302.FStar_Syntax_Syntax.ctx_uvar_range);
                                      FStar_Syntax_Syntax.ctx_uvar_meta =
                                        (uu___1674_76302.FStar_Syntax_Syntax.ctx_uvar_meta)
                                    }  in
                                  replace_cur
                                    (let uu___1677_76318 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___1677_76318.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___1677_76318.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___1677_76318.FStar_Tactics_Types.is_guard);
                                       FStar_Tactics_Types.label =
                                         (uu___1677_76318.FStar_Tactics_Types.label)
                                     })
                              | uu____76319 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____76321 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____76190
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____76351 =
        let uu____76354 = cur_goal ()  in
        bind uu____76354
          (fun goal  ->
             let uu____76365 = b  in
             match uu____76365 with
             | (bv,uu____76369) ->
                 let bv' =
                   let uu____76375 =
                     let uu___1688_76376 = bv  in
                     let uu____76377 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____76377;
                       FStar_Syntax_Syntax.index =
                         (uu___1688_76376.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___1688_76376.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____76375  in
                 let s1 =
                   let uu____76382 =
                     let uu____76383 =
                       let uu____76390 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____76390)  in
                     FStar_Syntax_Syntax.NT uu____76383  in
                   [uu____76382]  in
                 let uu____76395 = subst_goal bv bv' s1 goal  in
                 (match uu____76395 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____76351
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____76417 =
      let uu____76420 = cur_goal ()  in
      bind uu____76420
        (fun goal  ->
           let uu____76429 = b  in
           match uu____76429 with
           | (bv,uu____76433) ->
               let uu____76438 =
                 let uu____76449 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____76449  in
               (match uu____76438 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                    let uu____76476 = FStar_Syntax_Util.type_u ()  in
                    (match uu____76476 with
                     | (ty,u) ->
                         let uu____76485 = new_uvar "binder_retype" e0 ty  in
                         bind uu____76485
                           (fun uu____76504  ->
                              match uu____76504 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___1712_76514 = bv1  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1712_76514.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1712_76514.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____76518 =
                                      let uu____76519 =
                                        let uu____76526 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv1, uu____76526)  in
                                      FStar_Syntax_Syntax.NT uu____76519  in
                                    [uu____76518]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___1717_76538 = b1  in
                                         let uu____76539 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___1717_76538.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___1717_76538.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____76539
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____76546  ->
                                       let new_goal =
                                         let uu____76548 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____76549 =
                                           let uu____76550 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____76550
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____76548 uu____76549
                                          in
                                       let uu____76551 = add_goals [new_goal]
                                          in
                                       bind uu____76551
                                         (fun uu____76556  ->
                                            let uu____76557 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv1.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____76557
                                              goal.FStar_Tactics_Types.opts
                                              goal.FStar_Tactics_Types.label))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____76417
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____76583 =
        let uu____76586 = cur_goal ()  in
        bind uu____76586
          (fun goal  ->
             let uu____76595 = b  in
             match uu____76595 with
             | (bv,uu____76599) ->
                 let uu____76604 =
                   let uu____76615 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____76615  in
                 (match uu____76604 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                      let steps =
                        let uu____76645 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____76645
                         in
                      let sort' =
                        normalize steps e0 bv1.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___1738_76650 = bv1  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___1738_76650.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___1738_76650.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____76652 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____76652))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____76583
  
let (revert : unit -> unit tac) =
  fun uu____76665  ->
    let uu____76668 = cur_goal ()  in
    bind uu____76668
      (fun goal  ->
         let uu____76674 =
           let uu____76681 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____76681  in
         match uu____76674 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____76698 =
                 let uu____76701 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____76701  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____76698
                in
             let uu____76716 = new_uvar "revert" env' typ'  in
             bind uu____76716
               (fun uu____76732  ->
                  match uu____76732 with
                  | (r,u_r) ->
                      let uu____76741 =
                        let uu____76744 =
                          let uu____76745 =
                            let uu____76746 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____76746.FStar_Syntax_Syntax.pos  in
                          let uu____76749 =
                            let uu____76754 =
                              let uu____76755 =
                                let uu____76764 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____76764  in
                              [uu____76755]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____76754  in
                          uu____76749 FStar_Pervasives_Native.None
                            uu____76745
                           in
                        set_solution goal uu____76744  in
                      bind uu____76741
                        (fun uu____76785  ->
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
      let uu____76799 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____76799
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____76815 = cur_goal ()  in
    bind uu____76815
      (fun goal  ->
         mlog
           (fun uu____76823  ->
              let uu____76824 = FStar_Syntax_Print.binder_to_string b  in
              let uu____76826 =
                let uu____76828 =
                  let uu____76830 =
                    let uu____76839 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____76839  in
                  FStar_All.pipe_right uu____76830 FStar_List.length  in
                FStar_All.pipe_right uu____76828 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____76824 uu____76826)
           (fun uu____76860  ->
              let uu____76861 =
                let uu____76872 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____76872  in
              match uu____76861 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bv1,bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____76917 =
                          free_in bv1 bv'.FStar_Syntax_Syntax.sort  in
                        if uu____76917
                        then
                          let uu____76922 =
                            let uu____76924 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____76924
                             in
                          fail uu____76922
                        else check1 bvs2
                     in
                  let uu____76929 =
                    let uu____76931 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv1 uu____76931  in
                  if uu____76929
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____76938 = check1 bvs  in
                     bind uu____76938
                       (fun uu____76944  ->
                          let env' = push_bvs e' bvs  in
                          let uu____76946 =
                            let uu____76953 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____76953  in
                          bind uu____76946
                            (fun uu____76963  ->
                               match uu____76963 with
                               | (ut,uvar_ut) ->
                                   let uu____76972 = set_solution goal ut  in
                                   bind uu____76972
                                     (fun uu____76977  ->
                                        let uu____76978 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                            goal.FStar_Tactics_Types.label
                                           in
                                        replace_cur uu____76978))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____76986  ->
    let uu____76989 = cur_goal ()  in
    bind uu____76989
      (fun goal  ->
         let uu____76995 =
           let uu____77002 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____77002  in
         match uu____76995 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____77011) ->
             let uu____77016 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____77016)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____77029 = cur_goal ()  in
    bind uu____77029
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____77039 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____77039  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____77042  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____77055 = cur_goal ()  in
    bind uu____77055
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____77065 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____77065  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____77068  -> add_goals [g']))
  
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
            let uu____77109 = FStar_Syntax_Subst.compress t  in
            uu____77109.FStar_Syntax_Syntax.n  in
          let uu____77112 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___1922_77119 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___1922_77119.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___1922_77119.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____77112
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____77136 =
                   let uu____77137 = FStar_Syntax_Subst.compress t1  in
                   uu____77137.FStar_Syntax_Syntax.n  in
                 match uu____77136 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____77168 = ff hd1  in
                     bind uu____77168
                       (fun hd2  ->
                          let fa uu____77194 =
                            match uu____77194 with
                            | (a,q) ->
                                let uu____77215 = ff a  in
                                bind uu____77215 (fun a1  -> ret (a1, q))
                             in
                          let uu____77234 = mapM fa args  in
                          bind uu____77234
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____77316 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____77316 with
                      | (bs1,t') ->
                          let uu____77325 =
                            let uu____77328 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____77328 t'  in
                          bind uu____77325
                            (fun t''  ->
                               let uu____77332 =
                                 let uu____77333 =
                                   let uu____77352 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____77361 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____77352, uu____77361, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____77333  in
                               ret uu____77332))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____77436 = ff hd1  in
                     bind uu____77436
                       (fun hd2  ->
                          let ffb br =
                            let uu____77451 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____77451 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____77483 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____77483  in
                                let uu____77484 = ff1 e  in
                                bind uu____77484
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____77499 = mapM ffb brs  in
                          bind uu____77499
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____77543;
                          FStar_Syntax_Syntax.lbtyp = uu____77544;
                          FStar_Syntax_Syntax.lbeff = uu____77545;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____77547;
                          FStar_Syntax_Syntax.lbpos = uu____77548;_}::[]),e)
                     ->
                     let lb =
                       let uu____77576 =
                         let uu____77577 = FStar_Syntax_Subst.compress t1  in
                         uu____77577.FStar_Syntax_Syntax.n  in
                       match uu____77576 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____77581) -> lb
                       | uu____77597 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____77607 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____77607
                         (fun def1  ->
                            ret
                              (let uu___1875_77613 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1875_77613.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1875_77613.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1875_77613.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1875_77613.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1875_77613.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1875_77613.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____77614 = fflb lb  in
                     bind uu____77614
                       (fun lb1  ->
                          let uu____77624 =
                            let uu____77629 =
                              let uu____77630 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____77630]  in
                            FStar_Syntax_Subst.open_term uu____77629 e  in
                          match uu____77624 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____77660 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____77660  in
                              let uu____77661 = ff1 e1  in
                              bind uu____77661
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____77708 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____77708
                         (fun def  ->
                            ret
                              (let uu___1893_77714 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1893_77714.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1893_77714.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1893_77714.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1893_77714.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1893_77714.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1893_77714.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____77715 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____77715 with
                      | (lbs1,e1) ->
                          let uu____77730 = mapM fflb lbs1  in
                          bind uu____77730
                            (fun lbs2  ->
                               let uu____77742 = ff e1  in
                               bind uu____77742
                                 (fun e2  ->
                                    let uu____77750 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____77750 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____77821 = ff t2  in
                     bind uu____77821
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____77852 = ff t2  in
                     bind uu____77852
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____77859 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___1917_77866 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___1917_77866.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___1917_77866.FStar_Syntax_Syntax.vars)
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
              let uu____77913 =
                FStar_TypeChecker_TcTerm.tc_term
                  (let uu___1930_77922 = env  in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___1930_77922.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___1930_77922.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___1930_77922.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___1930_77922.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_sig =
                       (uu___1930_77922.FStar_TypeChecker_Env.gamma_sig);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___1930_77922.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___1930_77922.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___1930_77922.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___1930_77922.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.attrtab =
                       (uu___1930_77922.FStar_TypeChecker_Env.attrtab);
                     FStar_TypeChecker_Env.is_pattern =
                       (uu___1930_77922.FStar_TypeChecker_Env.is_pattern);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___1930_77922.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___1930_77922.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___1930_77922.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___1930_77922.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___1930_77922.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___1930_77922.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___1930_77922.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___1930_77922.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___1930_77922.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax = true;
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___1930_77922.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.phase1 =
                       (uu___1930_77922.FStar_TypeChecker_Env.phase1);
                     FStar_TypeChecker_Env.failhard =
                       (uu___1930_77922.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___1930_77922.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.uvar_subtyping =
                       (uu___1930_77922.FStar_TypeChecker_Env.uvar_subtyping);
                     FStar_TypeChecker_Env.tc_term =
                       (uu___1930_77922.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.type_of =
                       (uu___1930_77922.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___1930_77922.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.check_type_of =
                       (uu___1930_77922.FStar_TypeChecker_Env.check_type_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___1930_77922.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (uu___1930_77922.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (uu___1930_77922.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.fv_delta_depths =
                       (uu___1930_77922.FStar_TypeChecker_Env.fv_delta_depths);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___1930_77922.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (uu___1930_77922.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.splice =
                       (uu___1930_77922.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.postprocess =
                       (uu___1930_77922.FStar_TypeChecker_Env.postprocess);
                     FStar_TypeChecker_Env.is_native_tactic =
                       (uu___1930_77922.FStar_TypeChecker_Env.is_native_tactic);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___1930_77922.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (uu___1930_77922.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (uu___1930_77922.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.nbe =
                       (uu___1930_77922.FStar_TypeChecker_Env.nbe)
                   }) t
                 in
              match uu____77913 with
              | (t1,lcomp,g) ->
                  let uu____77929 =
                    (let uu____77933 =
                       FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                     Prims.op_Negation uu____77933) ||
                      (let uu____77936 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____77936)
                     in
                  if uu____77929
                  then ret t1
                  else
                    (let rewrite_eq =
                       let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                       let uu____77947 = new_uvar "pointwise_rec" env typ  in
                       bind uu____77947
                         (fun uu____77964  ->
                            match uu____77964 with
                            | (ut,uvar_ut) ->
                                (log ps
                                   (fun uu____77977  ->
                                      let uu____77978 =
                                        FStar_Syntax_Print.term_to_string t1
                                         in
                                      let uu____77980 =
                                        FStar_Syntax_Print.term_to_string ut
                                         in
                                      FStar_Util.print2
                                        "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                        uu____77978 uu____77980);
                                 (let uu____77983 =
                                    let uu____77986 =
                                      let uu____77987 =
                                        FStar_TypeChecker_TcTerm.universe_of
                                          env typ
                                         in
                                      FStar_Syntax_Util.mk_eq2 uu____77987
                                        typ t1 ut
                                       in
                                    add_irrelevant_goal
                                      "pointwise_rec equation" env
                                      uu____77986 opts label1
                                     in
                                  bind uu____77983
                                    (fun uu____77991  ->
                                       let uu____77992 =
                                         bind tau
                                           (fun uu____77998  ->
                                              let ut1 =
                                                FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                  env ut
                                                 in
                                              log ps
                                                (fun uu____78004  ->
                                                   let uu____78005 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1
                                                      in
                                                   let uu____78007 =
                                                     FStar_Syntax_Print.term_to_string
                                                       ut1
                                                      in
                                                   FStar_Util.print2
                                                     "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                     uu____78005 uu____78007);
                                              ret ut1)
                                          in
                                       focus uu____77992))))
                        in
                     let uu____78010 = catch rewrite_eq  in
                     bind uu____78010
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
          let uu____78228 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____78228
            (fun t1  ->
               let uu____78236 =
                 f env
                   (let uu___2007_78245 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___2007_78245.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___2007_78245.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____78236
                 (fun uu____78261  ->
                    match uu____78261 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____78284 =
                               let uu____78285 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____78285.FStar_Syntax_Syntax.n  in
                             match uu____78284 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____78322 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____78322
                                   (fun uu____78347  ->
                                      match uu____78347 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____78363 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____78363
                                            (fun uu____78390  ->
                                               match uu____78390 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___1987_78420 =
                                                         t3  in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___1987_78420.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___1987_78420.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____78462 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____78462 with
                                  | (bs1,t') ->
                                      let uu____78477 =
                                        let uu____78484 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____78484 ctrl1 t'
                                         in
                                      bind uu____78477
                                        (fun uu____78502  ->
                                           match uu____78502 with
                                           | (t'',ctrl2) ->
                                               let uu____78517 =
                                                 let uu____78524 =
                                                   let uu___2000_78527 = t4
                                                      in
                                                   let uu____78530 =
                                                     let uu____78531 =
                                                       let uu____78550 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____78559 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____78550,
                                                         uu____78559, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____78531
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____78530;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___2000_78527.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___2000_78527.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____78524, ctrl2)  in
                                               ret uu____78517))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____78612 -> ret (t3, ctrl1))))

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
              let uu____78659 = ctrl_tac_fold f env ctrl t  in
              bind uu____78659
                (fun uu____78683  ->
                   match uu____78683 with
                   | (t1,ctrl1) ->
                       let uu____78698 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____78698
                         (fun uu____78725  ->
                            match uu____78725 with
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
                let uu____78819 =
                  let uu____78827 =
                    add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                      opts label1
                     in
                  bind uu____78827
                    (fun uu____78838  ->
                       let uu____78839 = ctrl t1  in
                       bind uu____78839
                         (fun res  ->
                            let uu____78866 = trivial ()  in
                            bind uu____78866 (fun uu____78875  -> ret res)))
                   in
                bind uu____78819
                  (fun uu____78893  ->
                     match uu____78893 with
                     | (should_rewrite,ctrl1) ->
                         if Prims.op_Negation should_rewrite
                         then ret (t1, ctrl1)
                         else
                           (let uu____78922 =
                              FStar_TypeChecker_TcTerm.tc_term
                                (let uu___2037_78931 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___2037_78931.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___2037_78931.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___2037_78931.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___2037_78931.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___2037_78931.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___2037_78931.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___2037_78931.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___2037_78931.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___2037_78931.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___2037_78931.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___2037_78931.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___2037_78931.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___2037_78931.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___2037_78931.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___2037_78931.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___2037_78931.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___2037_78931.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___2037_78931.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___2037_78931.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___2037_78931.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___2037_78931.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___2037_78931.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___2037_78931.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___2037_78931.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___2037_78931.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___2037_78931.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___2037_78931.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___2037_78931.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___2037_78931.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___2037_78931.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___2037_78931.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___2037_78931.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___2037_78931.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___2037_78931.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___2037_78931.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___2037_78931.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___2037_78931.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___2037_78931.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___2037_78931.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___2037_78931.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___2037_78931.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___2037_78931.FStar_TypeChecker_Env.nbe)
                                 }) t1
                               in
                            match uu____78922 with
                            | (t2,lcomp,g) ->
                                let uu____78942 =
                                  (let uu____78946 =
                                     FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                       lcomp
                                      in
                                   Prims.op_Negation uu____78946) ||
                                    (let uu____78949 =
                                       FStar_TypeChecker_Env.is_trivial g  in
                                     Prims.op_Negation uu____78949)
                                   in
                                if uu____78942
                                then ret (t2, globalStop)
                                else
                                  (let typ =
                                     lcomp.FStar_Syntax_Syntax.res_typ  in
                                   let uu____78965 =
                                     new_uvar "pointwise_rec" env typ  in
                                   bind uu____78965
                                     (fun uu____78986  ->
                                        match uu____78986 with
                                        | (ut,uvar_ut) ->
                                            (log ps
                                               (fun uu____79003  ->
                                                  let uu____79004 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t2
                                                     in
                                                  let uu____79006 =
                                                    FStar_Syntax_Print.term_to_string
                                                      ut
                                                     in
                                                  FStar_Util.print2
                                                    "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                    uu____79004 uu____79006);
                                             (let uu____79009 =
                                                let uu____79012 =
                                                  let uu____79013 =
                                                    FStar_TypeChecker_TcTerm.universe_of
                                                      env typ
                                                     in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____79013 typ t2 ut
                                                   in
                                                add_irrelevant_goal
                                                  "rewrite_rec equation" env
                                                  uu____79012 opts label1
                                                 in
                                              bind uu____79009
                                                (fun uu____79021  ->
                                                   let uu____79022 =
                                                     bind rewriter
                                                       (fun uu____79036  ->
                                                          let ut1 =
                                                            FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                              env ut
                                                             in
                                                          log ps
                                                            (fun uu____79042 
                                                               ->
                                                               let uu____79043
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   t2
                                                                  in
                                                               let uu____79045
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   ut1
                                                                  in
                                                               FStar_Util.print2
                                                                 "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                                 uu____79043
                                                                 uu____79045);
                                                          ret (ut1, ctrl1))
                                                      in
                                                   focus uu____79022)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term -> (Prims.bool * FStar_BigInt.t) tac) ->
    unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____79091 =
        bind get
          (fun ps  ->
             let uu____79101 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____79101 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____79139  ->
                       let uu____79140 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____79140);
                  bind dismiss_all
                    (fun uu____79145  ->
                       let uu____79146 =
                         let uu____79153 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____79153
                           keepGoing gt1
                          in
                       bind uu____79146
                         (fun uu____79165  ->
                            match uu____79165 with
                            | (gt',uu____79173) ->
                                (log ps
                                   (fun uu____79177  ->
                                      let uu____79178 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____79178);
                                 (let uu____79181 = push_goals gs  in
                                  bind uu____79181
                                    (fun uu____79186  ->
                                       let uu____79187 =
                                         let uu____79190 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____79190]  in
                                       add_goals uu____79187)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____79091
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____79215 =
        bind get
          (fun ps  ->
             let uu____79225 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____79225 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____79263  ->
                       let uu____79264 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____79264);
                  bind dismiss_all
                    (fun uu____79269  ->
                       let uu____79270 =
                         let uu____79273 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____79273 gt1
                          in
                       bind uu____79270
                         (fun gt'  ->
                            log ps
                              (fun uu____79281  ->
                                 let uu____79282 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____79282);
                            (let uu____79285 = push_goals gs  in
                             bind uu____79285
                               (fun uu____79290  ->
                                  let uu____79291 =
                                    let uu____79294 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____79294]  in
                                  add_goals uu____79291))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____79215
  
let (trefl : unit -> unit tac) =
  fun uu____79307  ->
    let uu____79310 =
      let uu____79313 = cur_goal ()  in
      bind uu____79313
        (fun g  ->
           let uu____79331 =
             let uu____79336 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____79336  in
           match uu____79331 with
           | FStar_Pervasives_Native.Some t ->
               let uu____79344 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____79344 with
                | (hd1,args) ->
                    let uu____79383 =
                      let uu____79396 =
                        let uu____79397 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____79397.FStar_Syntax_Syntax.n  in
                      (uu____79396, args)  in
                    (match uu____79383 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____79411::(l,uu____79413)::(r,uu____79415)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____79462 =
                           let uu____79466 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____79466 l r  in
                         bind uu____79462
                           (fun b  ->
                              if b
                              then solve' g FStar_Syntax_Util.exp_unit
                              else
                                (let l1 =
                                   let uu____79477 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____79477 l
                                    in
                                 let r1 =
                                   let uu____79479 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____79479 r
                                    in
                                 let uu____79480 =
                                   let uu____79484 =
                                     FStar_Tactics_Types.goal_env g  in
                                   do_unify uu____79484 l1 r1  in
                                 bind uu____79480
                                   (fun b1  ->
                                      if b1
                                      then
                                        solve' g FStar_Syntax_Util.exp_unit
                                      else
                                        (let uu____79494 =
                                           let uu____79496 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____79496 l1  in
                                         let uu____79497 =
                                           let uu____79499 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____79499 r1  in
                                         fail2
                                           "not a trivial equality ((%s) vs (%s))"
                                           uu____79494 uu____79497))))
                     | (hd2,uu____79502) ->
                         let uu____79519 =
                           let uu____79521 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____79521 t  in
                         fail1 "trefl: not an equality (%s)" uu____79519))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____79310
  
let (dup : unit -> unit tac) =
  fun uu____79538  ->
    let uu____79541 = cur_goal ()  in
    bind uu____79541
      (fun g  ->
         let uu____79547 =
           let uu____79554 = FStar_Tactics_Types.goal_env g  in
           let uu____79555 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____79554 uu____79555  in
         bind uu____79547
           (fun uu____79565  ->
              match uu____79565 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___2129_79575 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___2129_79575.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___2129_79575.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___2129_79575.FStar_Tactics_Types.is_guard);
                      FStar_Tactics_Types.label =
                        (uu___2129_79575.FStar_Tactics_Types.label)
                    }  in
                  bind __dismiss
                    (fun uu____79578  ->
                       let uu____79579 =
                         let uu____79582 = FStar_Tactics_Types.goal_env g  in
                         let uu____79583 =
                           let uu____79584 =
                             let uu____79585 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____79586 =
                               FStar_Tactics_Types.goal_type g  in
                             FStar_TypeChecker_TcTerm.universe_of uu____79585
                               uu____79586
                              in
                           let uu____79587 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____79588 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____79584 uu____79587 u
                             uu____79588
                            in
                         add_irrelevant_goal "dup equation" uu____79582
                           uu____79583 g.FStar_Tactics_Types.opts
                           g.FStar_Tactics_Types.label
                          in
                       bind uu____79579
                         (fun uu____79592  ->
                            let uu____79593 = add_goals [g']  in
                            bind uu____79593 (fun uu____79597  -> ret ())))))
  
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
              let uu____79723 = f x y  in
              if uu____79723 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____79746 -> (acc, l11, l21)  in
        let uu____79761 = aux [] l1 l2  in
        match uu____79761 with | (pr,t1,t2) -> ((FStar_List.rev pr), t1, t2)
  
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
      let uu____79867 = get_phi g1  in
      match uu____79867 with
      | FStar_Pervasives_Native.None  -> fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____79874 = get_phi g2  in
          (match uu____79874 with
           | FStar_Pervasives_Native.None  -> fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let uu____79887 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2)
                  in
               (match uu____79887 with
                | (gamma,r1,r2) ->
                    let t1 =
                      let uu____79918 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1)
                         in
                      close_forall_no_univs1 uu____79918 phi1  in
                    let t2 =
                      let uu____79928 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2)
                         in
                      close_forall_no_univs1 uu____79928 phi2  in
                    let uu____79937 =
                      set_solution g1 FStar_Syntax_Util.exp_unit  in
                    bind uu____79937
                      (fun uu____79942  ->
                         let uu____79943 =
                           set_solution g2 FStar_Syntax_Util.exp_unit  in
                         bind uu____79943
                           (fun uu____79950  ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2  in
                              let nenv =
                                let uu___2180_79955 =
                                  FStar_Tactics_Types.goal_env g1  in
                                let uu____79956 =
                                  FStar_Util.smap_create
                                    (Prims.parse_int "100")
                                   in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___2180_79955.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___2180_79955.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___2180_79955.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___2180_79955.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____79956;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___2180_79955.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___2180_79955.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___2180_79955.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___2180_79955.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___2180_79955.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___2180_79955.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___2180_79955.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___2180_79955.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___2180_79955.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___2180_79955.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___2180_79955.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___2180_79955.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___2180_79955.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___2180_79955.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___2180_79955.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___2180_79955.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___2180_79955.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___2180_79955.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___2180_79955.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___2180_79955.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___2180_79955.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___2180_79955.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___2180_79955.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___2180_79955.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___2180_79955.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___2180_79955.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___2180_79955.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___2180_79955.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___2180_79955.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___2180_79955.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___2180_79955.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___2180_79955.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___2180_79955.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___2180_79955.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___2180_79955.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___2180_79955.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___2180_79955.FStar_TypeChecker_Env.nbe)
                                }  in
                              let uu____79960 =
                                mk_irrelevant_goal "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                  g1.FStar_Tactics_Types.label
                                 in
                              bind uu____79960
                                (fun goal  ->
                                   mlog
                                     (fun uu____79970  ->
                                        let uu____79971 =
                                          goal_to_string_verbose g1  in
                                        let uu____79973 =
                                          goal_to_string_verbose g2  in
                                        let uu____79975 =
                                          goal_to_string_verbose goal  in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____79971 uu____79973 uu____79975)
                                     (fun uu____79979  -> ret goal))))))
  
let (join : unit -> unit tac) =
  fun uu____79987  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____80003 =
               set
                 (let uu___2195_80008 = ps  in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___2195_80008.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.main_goal =
                      (uu___2195_80008.FStar_Tactics_Types.main_goal);
                    FStar_Tactics_Types.all_implicits =
                      (uu___2195_80008.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___2195_80008.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___2195_80008.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___2195_80008.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___2195_80008.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___2195_80008.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___2195_80008.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___2195_80008.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___2195_80008.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___2195_80008.FStar_Tactics_Types.local_state)
                  })
                in
             bind uu____80003
               (fun uu____80011  ->
                  let uu____80012 = join_goals g1 g2  in
                  bind uu____80012 (fun g12  -> add_goals [g12]))
         | uu____80017 -> fail "join: less than 2 goals")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) tac)
  =
  fun t  ->
    let uu____80039 =
      let uu____80046 = cur_goal ()  in
      bind uu____80046
        (fun g  ->
           let uu____80056 =
             let uu____80065 = FStar_Tactics_Types.goal_env g  in
             __tc uu____80065 t  in
           bind uu____80056
             (fun uu____80093  ->
                match uu____80093 with
                | (t1,typ,guard) ->
                    let uu____80109 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____80109 with
                     | (hd1,args) ->
                         let uu____80158 =
                           let uu____80173 =
                             let uu____80174 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____80174.FStar_Syntax_Syntax.n  in
                           (uu____80173, args)  in
                         (match uu____80158 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____80195)::(q,uu____80197)::[]) when
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
                                let uu____80251 =
                                  let uu____80252 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____80252
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____80251
                                 in
                              let g2 =
                                let uu____80254 =
                                  let uu____80255 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____80255
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____80254
                                 in
                              bind __dismiss
                                (fun uu____80262  ->
                                   let uu____80263 = add_goals [g1; g2]  in
                                   bind uu____80263
                                     (fun uu____80272  ->
                                        let uu____80273 =
                                          let uu____80278 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____80279 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____80278, uu____80279)  in
                                        ret uu____80273))
                          | uu____80284 ->
                              let uu____80299 =
                                let uu____80301 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____80301 typ  in
                              fail1 "Not a disjunction: %s" uu____80299))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____80039
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____80336 =
      let uu____80339 = cur_goal ()  in
      bind uu____80339
        (fun g  ->
           FStar_Options.push ();
           (let uu____80352 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____80352);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___2232_80359 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___2232_80359.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___2232_80359.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___2232_80359.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___2232_80359.FStar_Tactics_Types.label)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____80336
  
let (top_env : unit -> env tac) =
  fun uu____80376  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____80391  ->
    let uu____80395 = cur_goal ()  in
    bind uu____80395
      (fun g  ->
         let uu____80402 =
           (FStar_Options.lax ()) ||
             (let uu____80405 = FStar_Tactics_Types.goal_env g  in
              uu____80405.FStar_TypeChecker_Env.lax)
            in
         ret uu____80402)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____80422 =
        mlog
          (fun uu____80427  ->
             let uu____80428 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____80428)
          (fun uu____80433  ->
             let uu____80434 = cur_goal ()  in
             bind uu____80434
               (fun goal  ->
                  let env =
                    let uu____80442 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____80442 ty  in
                  let uu____80443 = __tc_ghost env tm  in
                  bind uu____80443
                    (fun uu____80462  ->
                       match uu____80462 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____80476  ->
                                let uu____80477 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____80477)
                             (fun uu____80481  ->
                                mlog
                                  (fun uu____80484  ->
                                     let uu____80485 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____80485)
                                  (fun uu____80490  ->
                                     let uu____80491 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____80491
                                       (fun uu____80496  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____80422
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____80521 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____80527 =
              let uu____80534 =
                let uu____80535 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____80535
                 in
              new_uvar "uvar_env.2" env uu____80534  in
            bind uu____80527
              (fun uu____80552  ->
                 match uu____80552 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____80521
        (fun typ  ->
           let uu____80564 = new_uvar "uvar_env" env typ  in
           bind uu____80564
             (fun uu____80579  ->
                match uu____80579 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____80598 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____80617 -> g.FStar_Tactics_Types.opts
             | uu____80620 -> FStar_Options.peek ()  in
           let uu____80623 = FStar_Syntax_Util.head_and_args t  in
           match uu____80623 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____80643);
                FStar_Syntax_Syntax.pos = uu____80644;
                FStar_Syntax_Syntax.vars = uu____80645;_},uu____80646)
               ->
               let env1 =
                 let uu___2286_80688 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___2286_80688.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___2286_80688.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___2286_80688.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___2286_80688.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___2286_80688.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___2286_80688.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___2286_80688.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___2286_80688.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___2286_80688.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___2286_80688.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___2286_80688.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___2286_80688.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___2286_80688.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___2286_80688.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___2286_80688.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___2286_80688.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___2286_80688.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___2286_80688.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___2286_80688.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___2286_80688.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___2286_80688.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___2286_80688.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___2286_80688.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___2286_80688.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___2286_80688.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___2286_80688.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___2286_80688.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___2286_80688.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___2286_80688.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___2286_80688.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___2286_80688.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___2286_80688.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___2286_80688.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___2286_80688.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___2286_80688.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___2286_80688.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___2286_80688.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___2286_80688.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___2286_80688.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___2286_80688.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___2286_80688.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___2286_80688.FStar_TypeChecker_Env.nbe)
                 }  in
               let g =
                 FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false ""  in
               let uu____80692 =
                 let uu____80695 = bnorm_goal g  in [uu____80695]  in
               add_goals uu____80692
           | uu____80696 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____80598
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____80758 = if b then t2 else ret false  in
             bind uu____80758 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____80784 = trytac comp  in
      bind uu____80784
        (fun uu___613_80796  ->
           match uu___613_80796 with
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
        let uu____80838 =
          bind get
            (fun ps  ->
               let uu____80846 = __tc e t1  in
               bind uu____80846
                 (fun uu____80867  ->
                    match uu____80867 with
                    | (t11,ty1,g1) ->
                        let uu____80880 = __tc e t2  in
                        bind uu____80880
                          (fun uu____80901  ->
                             match uu____80901 with
                             | (t21,ty2,g2) ->
                                 let uu____80914 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____80914
                                   (fun uu____80921  ->
                                      let uu____80922 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____80922
                                        (fun uu____80930  ->
                                           let uu____80931 =
                                             do_unify e ty1 ty2  in
                                           let uu____80935 =
                                             do_unify e t11 t21  in
                                           tac_and uu____80931 uu____80935)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____80838
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____80983  ->
             let uu____80984 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____80984
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
        (fun uu____81018  ->
           let uu____81019 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____81019)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____81030 =
      mlog
        (fun uu____81035  ->
           let uu____81036 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____81036)
        (fun uu____81041  ->
           let uu____81042 = cur_goal ()  in
           bind uu____81042
             (fun g  ->
                let uu____81048 =
                  let uu____81057 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____81057 ty  in
                bind uu____81048
                  (fun uu____81069  ->
                     match uu____81069 with
                     | (ty1,uu____81079,guard) ->
                         let uu____81081 =
                           let uu____81084 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____81084 guard  in
                         bind uu____81081
                           (fun uu____81088  ->
                              let uu____81089 =
                                let uu____81093 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____81094 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____81093 uu____81094 ty1  in
                              bind uu____81089
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____81103 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____81103
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops]  in
                                      let ng =
                                        let uu____81110 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____81111 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____81110
                                          uu____81111
                                         in
                                      let nty =
                                        let uu____81113 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____81113 ty1  in
                                      let uu____81114 =
                                        let uu____81118 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____81118 ng nty  in
                                      bind uu____81114
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____81127 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____81127
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____81030
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) Prims.list tac)
  =
  fun s_tm  ->
    let uu____81201 =
      let uu____81210 = cur_goal ()  in
      bind uu____81210
        (fun g  ->
           let uu____81222 =
             let uu____81231 = FStar_Tactics_Types.goal_env g  in
             __tc uu____81231 s_tm  in
           bind uu____81222
             (fun uu____81249  ->
                match uu____81249 with
                | (s_tm1,s_ty,guard) ->
                    let uu____81267 =
                      let uu____81270 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____81270 guard  in
                    bind uu____81267
                      (fun uu____81283  ->
                         let uu____81284 =
                           FStar_Syntax_Util.head_and_args' s_ty  in
                         match uu____81284 with
                         | (h,args) ->
                             let uu____81329 =
                               let uu____81336 =
                                 let uu____81337 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____81337.FStar_Syntax_Syntax.n  in
                               match uu____81336 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____81352;
                                      FStar_Syntax_Syntax.vars = uu____81353;_},us)
                                   -> ret (fv, us)
                               | uu____81363 -> fail "type is not an fv"  in
                             bind uu____81329
                               (fun uu____81384  ->
                                  match uu____81384 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____81400 =
                                        let uu____81403 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____81403 t_lid
                                         in
                                      (match uu____81400 with
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
                                                  (fun uu____81454  ->
                                                     let uu____81455 =
                                                       FStar_Syntax_Subst.open_term
                                                         t_ps t_ty
                                                        in
                                                     match uu____81455 with
                                                     | (t_ps1,t_ty1) ->
                                                         let uu____81470 =
                                                           mapM
                                                             (fun c_lid  ->
                                                                let uu____81498
                                                                  =
                                                                  let uu____81501
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                  FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____81501
                                                                    c_lid
                                                                   in
                                                                match uu____81498
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
                                                                    uu____81575
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
                                                                    let uu____81580
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____81580
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____81603
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____81603
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____81646
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs
                                                                     in
                                                                    (match uu____81646
                                                                    with
                                                                    | 
                                                                    (d_ps,bs1)
                                                                    ->
                                                                    let uu____81719
                                                                    =
                                                                    let uu____81721
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp  in
                                                                    Prims.op_Negation
                                                                    uu____81721
                                                                     in
                                                                    failwhen
                                                                    uu____81719
                                                                    "not total?"
                                                                    (fun
                                                                    uu____81740
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
                                                                    uu___614_81757
                                                                    =
                                                                    match uu___614_81757
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____81761)
                                                                    -> true
                                                                    | 
                                                                    uu____81764
                                                                    -> false
                                                                     in
                                                                    let uu____81768
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____81768
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
                                                                    uu____81902
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
                                                                    uu____81964
                                                                     ->
                                                                    match uu____81964
                                                                    with
                                                                    | 
                                                                    ((bv,uu____81984),
                                                                    (t,uu____81986))
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
                                                                    uu____82056
                                                                     ->
                                                                    match uu____82056
                                                                    with
                                                                    | 
                                                                    ((bv,uu____82083),
                                                                    (t,uu____82085))
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
                                                                    uu____82144
                                                                     ->
                                                                    match uu____82144
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
                                                                    let uu____82199
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___2450_82216
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___2450_82216.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___2450_82216.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___2450_82216.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___2450_82216.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___2450_82216.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___2450_82216.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___2450_82216.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___2450_82216.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___2450_82216.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___2450_82216.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___2450_82216.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___2450_82216.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___2450_82216.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___2450_82216.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___2450_82216.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___2450_82216.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___2450_82216.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___2450_82216.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___2450_82216.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___2450_82216.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___2450_82216.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___2450_82216.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___2450_82216.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___2450_82216.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___2450_82216.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___2450_82216.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___2450_82216.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___2450_82216.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___2450_82216.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___2450_82216.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___2450_82216.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___2450_82216.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___2450_82216.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___2450_82216.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___2450_82216.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___2450_82216.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___2450_82216.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___2450_82216.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___2450_82216.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___2450_82216.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___2450_82216.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___2450_82216.FStar_TypeChecker_Env.nbe)
                                                                    }) s_ty
                                                                    pat  in
                                                                    match uu____82199
                                                                    with
                                                                    | 
                                                                    (uu____82230,uu____82231,uu____82232,pat_t,uu____82234,_guard_pat)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____82241
                                                                    =
                                                                    let uu____82242
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____82242
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____82241
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____82247
                                                                    =
                                                                    let uu____82256
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____82256]
                                                                     in
                                                                    let uu____82275
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____82247
                                                                    uu____82275
                                                                     in
                                                                    let nty =
                                                                    let uu____82281
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____82281
                                                                     in
                                                                    let uu____82284
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____82284
                                                                    (fun
                                                                    uu____82314
                                                                     ->
                                                                    match uu____82314
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
                                                                    let uu____82341
                                                                    =
                                                                    let uu____82352
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____82352]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____82341
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____82388
                                                                    =
                                                                    let uu____82399
                                                                    =
                                                                    let uu____82404
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2)  in
                                                                    (fv1,
                                                                    uu____82404)
                                                                     in
                                                                    (g', br,
                                                                    uu____82399)
                                                                     in
                                                                    ret
                                                                    uu____82388))))))
                                                                    | 
                                                                    uu____82425
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                             c_lids
                                                            in
                                                         bind uu____81470
                                                           (fun goal_brs  ->
                                                              let uu____82475
                                                                =
                                                                FStar_List.unzip3
                                                                  goal_brs
                                                                 in
                                                              match uu____82475
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
                                                                  let uu____82548
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                  bind
                                                                    uu____82548
                                                                    (
                                                                    fun
                                                                    uu____82559
                                                                     ->
                                                                    let uu____82560
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____82560
                                                                    (fun
                                                                    uu____82570
                                                                     ->
                                                                    ret infos))))
                                            | uu____82577 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____81201
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____82626::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____82656 = init xs  in x :: uu____82656
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____82669 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      let t3 = FStar_Syntax_Util.unlazy_emb t2  in
      match t3.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____82678) -> inspect t4
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____82744 = last args  in
          (match uu____82744 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____82774 =
                 let uu____82775 =
                   let uu____82780 =
                     let uu____82781 =
                       let uu____82786 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____82786  in
                     uu____82781 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____82780, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____82775  in
               FStar_All.pipe_left ret uu____82774)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____82799,uu____82800) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
          let uu____82853 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____82853 with
           | (bs1,t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____82895 =
                      let uu____82896 =
                        let uu____82901 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____82901)  in
                      FStar_Reflection_Data.Tv_Abs uu____82896  in
                    FStar_All.pipe_left ret uu____82895))
      | FStar_Syntax_Syntax.Tm_type uu____82904 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____82929 ->
          let uu____82944 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____82944 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____82975 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____82975 with
           | (b',t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____83028 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____83041 =
            let uu____83042 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____83042  in
          FStar_All.pipe_left ret uu____83041
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____83063 =
            let uu____83064 =
              let uu____83069 =
                let uu____83070 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____83070  in
              (uu____83069, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____83064  in
          FStar_All.pipe_left ret uu____83063
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____83110 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____83115 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____83115 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____83168 ->
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
             | FStar_Util.Inr uu____83210 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____83214 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____83214 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____83234 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____83240 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____83295 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____83295
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____83316 =
                  let uu____83323 =
                    FStar_List.map
                      (fun uu____83336  ->
                         match uu____83336 with
                         | (p1,uu____83345) -> inspect_pat p1) ps
                     in
                  (fv, uu____83323)  in
                FStar_Reflection_Data.Pat_Cons uu____83316
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
              (fun uu___615_83441  ->
                 match uu___615_83441 with
                 | (pat,uu____83463,t5) ->
                     let uu____83481 = inspect_pat pat  in (uu____83481, t5))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____83490 ->
          ((let uu____83492 =
              let uu____83498 =
                let uu____83500 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____83502 = FStar_Syntax_Print.term_to_string t3  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____83500 uu____83502
                 in
              (FStar_Errors.Warning_CantInspect, uu____83498)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____83492);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____82669
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____83520 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____83520
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____83524 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____83524
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____83528 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____83528
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____83535 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____83535
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____83560 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____83560
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____83577 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____83577
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____83596 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____83596
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____83600 =
          let uu____83601 =
            let uu____83608 =
              let uu____83609 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____83609  in
            FStar_Syntax_Syntax.mk uu____83608  in
          uu____83601 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____83600
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____83617 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____83617
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____83628 =
          let uu____83629 =
            let uu____83636 =
              let uu____83637 =
                let uu____83651 =
                  let uu____83654 =
                    let uu____83655 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____83655]  in
                  FStar_Syntax_Subst.close uu____83654 t2  in
                ((false, [lb]), uu____83651)  in
              FStar_Syntax_Syntax.Tm_let uu____83637  in
            FStar_Syntax_Syntax.mk uu____83636  in
          uu____83629 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____83628
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____83700 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____83700 with
         | (lbs,body) ->
             let uu____83715 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____83715)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____83752 =
                let uu____83753 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____83753  in
              FStar_All.pipe_left wrap uu____83752
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____83760 =
                let uu____83761 =
                  let uu____83775 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____83793 = pack_pat p1  in
                         (uu____83793, false)) ps
                     in
                  (fv, uu____83775)  in
                FStar_Syntax_Syntax.Pat_cons uu____83761  in
              FStar_All.pipe_left wrap uu____83760
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
            (fun uu___616_83842  ->
               match uu___616_83842 with
               | (pat,t1) ->
                   let uu____83859 = pack_pat pat  in
                   (uu____83859, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____83907 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____83907
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____83935 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____83935
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____83981 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____83981
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____84020 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____84020
  
let (lget :
  FStar_Reflection_Data.typ -> Prims.string -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun k  ->
      let uu____84040 =
        bind get
          (fun ps  ->
             let uu____84046 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____84046 with
             | FStar_Pervasives_Native.None  -> fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
      FStar_All.pipe_left (wrap_err "lget") uu____84040
  
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit tac)
  =
  fun _ty  ->
    fun k  ->
      fun t  ->
        let uu____84080 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___2748_84087 = ps  in
                 let uu____84088 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t
                    in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___2748_84087.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___2748_84087.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___2748_84087.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___2748_84087.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___2748_84087.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___2748_84087.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___2748_84087.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___2748_84087.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___2748_84087.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___2748_84087.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___2748_84087.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___2748_84087.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____84088
                 }  in
               set ps1)
           in
        FStar_All.pipe_left (wrap_err "lset") uu____84080
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal * FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun typ  ->
      let uu____84115 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____84115 with
      | (u,ctx_uvars,g_u) ->
          let uu____84148 = FStar_List.hd ctx_uvars  in
          (match uu____84148 with
           | (ctx_uvar,uu____84162) ->
               let g =
                 let uu____84164 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____84164 false
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
        let uu____84187 = goal_of_goal_ty env typ  in
        match uu____84187 with
        | (g,g_u) ->
            let ps =
              let uu____84199 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "TacVerbose")
                 in
              let uu____84202 = FStar_Util.psmap_empty ()  in
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
                FStar_Tactics_Types.tac_verb_dbg = uu____84199;
                FStar_Tactics_Types.local_state = uu____84202
              }  in
            let uu____84212 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____84212)
  