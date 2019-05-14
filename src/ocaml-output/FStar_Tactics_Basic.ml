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
    let uu____578 =
      let uu____587 = FStar_Tactics_Types.goal_env g  in
      let uu____696 = FStar_Tactics_Types.goal_type g  in
      bnorm uu____587 uu____696  in
    FStar_Tactics_Types.goal_with_type g uu____578
  
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
      let uu____1442 = FStar_Options.tactics_failhard ()  in
      if uu____1442
      then run t p
      else
        (try (fun uu___31_1452  -> match () with | () -> run t p) ()
         with
         | FStar_Errors.Err (uu____1461,msg) ->
             FStar_Tactics_Result.Failed
               ((FStar_Tactics_Types.TacticFailure msg), p)
         | FStar_Errors.Error (uu____1532,msg,uu____1534) ->
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
           let uu____2095 = run t1 p  in
           match uu____2095 with
           | FStar_Tactics_Result.Success (a,q) ->
               let uu____2236 = t2 a  in run uu____2236 q
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
    let uu____2961 =
      FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head  in
    match uu____2961 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (check_goal_solved :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun goal  -> get_uvar_solved goal.FStar_Tactics_Types.goal_ctx_uvar 
let (goal_to_string_verbose : FStar_Tactics_Types.goal -> Prims.string) =
  fun g  ->
    let uu____3251 =
      FStar_Syntax_Print.ctx_uvar_to_string
        g.FStar_Tactics_Types.goal_ctx_uvar
       in
    let uu____3253 =
      let uu____3255 = check_goal_solved g  in
      match uu____3255 with
      | FStar_Pervasives_Native.None  -> ""
      | FStar_Pervasives_Native.Some t ->
          let uu____3277 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "\tGOAL ALREADY SOLVED!: %s" uu____3277
       in
    FStar_Util.format2 "%s%s\n" uu____3251 uu____3253
  
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
            let uu____3576 = FStar_Options.print_implicits ()  in
            if uu____3576
            then
              let uu____3580 = FStar_Tactics_Types.goal_env g  in
              let uu____3689 = FStar_Tactics_Types.goal_witness g  in
              tts uu____3580 uu____3689
            else
              (let uu____3700 =
                 get_uvar_solved g.FStar_Tactics_Types.goal_ctx_uvar  in
               match uu____3700 with
               | FStar_Pervasives_Native.None  -> "_"
               | FStar_Pervasives_Native.Some t ->
                   let uu____3722 = FStar_Tactics_Types.goal_env g  in
                   let uu____3831 = FStar_Tactics_Types.goal_witness g  in
                   tts uu____3722 uu____3831)
             in
          let num =
            match maybe_num with
            | FStar_Pervasives_Native.None  -> ""
            | FStar_Pervasives_Native.Some (i,n1) ->
                let uu____3862 = FStar_Util.string_of_int i  in
                let uu____3864 = FStar_Util.string_of_int n1  in
                FStar_Util.format2 " %s/%s" uu____3862 uu____3864
             in
          let maybe_label =
            match g.FStar_Tactics_Types.label with
            | "" -> ""
            | l -> Prims.op_Hat " (" (Prims.op_Hat l ")")  in
          let actual_goal =
            if ps.FStar_Tactics_Types.tac_verb_dbg
            then goal_to_string_verbose g
            else
              (let uu____3882 =
                 FStar_Syntax_Print.binders_to_string ", "
                   (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
                  in
               let uu____3885 =
                 let uu____3887 = FStar_Tactics_Types.goal_env g  in
                 tts uu____3887
                   (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                  in
               FStar_Util.format3 "%s |- %s : %s\n" uu____3882 w uu____3885)
             in
          FStar_Util.format4 "%s%s%s:\n%s\n" kind num maybe_label actual_goal
  
let (tacprint : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      let uu____4022 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____4022
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____4047 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____4047
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____4079 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____4079
  
let (get_phi :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun g  ->
    let uu____4218 =
      let uu____4227 = FStar_Tactics_Types.goal_env g  in
      let uu____4336 = FStar_Tactics_Types.goal_type g  in
      FStar_TypeChecker_Normalize.unfold_whnf uu____4227 uu____4336  in
    FStar_Syntax_Util.un_squash uu____4218
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  -> let uu____4471 = get_phi g  in FStar_Option.isSome uu____4471 
let (print : Prims.string -> unit tac) = fun msg  -> tacprint msg; ret () 
let (debugging : unit -> Prims.bool tac) =
  fun uu____4512  ->
    bind get
      (fun ps  ->
         let uu____4657 =
           FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
             (FStar_Options.Other "Tac")
            in
         ret uu____4657)
  
let (ps_to_string :
  (Prims.string * FStar_Tactics_Types.proofstate) -> Prims.string) =
  fun uu____4739  ->
    match uu____4739 with
    | (msg,ps) ->
        let p_imp imp =
          FStar_Syntax_Print.uvar_to_string
            (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
           in
        let n_active = FStar_List.length ps.FStar_Tactics_Types.goals  in
        let n_smt = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
        let n1 = n_active + n_smt  in
        let uu____5088 =
          let uu____5092 =
            let uu____5096 =
              let uu____5098 =
                FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
              FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____5098
                msg
               in
            let uu____5101 =
              let uu____5105 =
                if
                  ps.FStar_Tactics_Types.entry_range <>
                    FStar_Range.dummyRange
                then
                  let uu____5109 =
                    FStar_Range.string_of_def_range
                      ps.FStar_Tactics_Types.entry_range
                     in
                  FStar_Util.format1 "Location: %s\n" uu____5109
                else ""  in
              let uu____5115 =
                let uu____5119 =
                  let uu____5121 =
                    FStar_TypeChecker_Env.debug
                      ps.FStar_Tactics_Types.main_context
                      (FStar_Options.Other "Imp")
                     in
                  if uu____5121
                  then
                    let uu____5126 =
                      FStar_Common.string_of_list p_imp
                        ps.FStar_Tactics_Types.all_implicits
                       in
                    FStar_Util.format1 "Imps: %s\n" uu____5126
                  else ""  in
                [uu____5119]  in
              uu____5105 :: uu____5115  in
            uu____5096 :: uu____5101  in
          let uu____5140 =
            let uu____5144 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "Goal"
                       (FStar_Pervasives_Native.Some
                          (((Prims.parse_int "1") + i), n1)) ps g)
                ps.FStar_Tactics_Types.goals
               in
            let uu____5282 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "SMT Goal"
                       (FStar_Pervasives_Native.Some
                          ((((Prims.parse_int "1") + n_active) + i), n1)) ps
                       g) ps.FStar_Tactics_Types.smt_goals
               in
            FStar_List.append uu____5144 uu____5282  in
          FStar_List.append uu____5092 uu____5140  in
        FStar_String.concat "" uu____5088
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      let uu____5548 =
        let uu____5549 = FStar_Tactics_Types.goal_env g  in
        FStar_TypeChecker_Env.all_binders uu____5549  in
      let uu____5658 =
        let uu____5663 =
          let uu____5664 = FStar_Tactics_Types.goal_env g  in
          FStar_TypeChecker_Env.dsenv uu____5664  in
        FStar_Syntax_Print.binders_to_json uu____5663  in
      FStar_All.pipe_right uu____5548 uu____5658  in
    let uu____5773 =
      let uu____5781 =
        let uu____5789 =
          let uu____5795 =
            let uu____5796 =
              let uu____5804 =
                let uu____5810 =
                  let uu____5811 =
                    let uu____5813 = FStar_Tactics_Types.goal_env g  in
                    let uu____5922 = FStar_Tactics_Types.goal_witness g  in
                    tts uu____5813 uu____5922  in
                  FStar_Util.JsonStr uu____5811  in
                ("witness", uu____5810)  in
              let uu____5933 =
                let uu____5941 =
                  let uu____5947 =
                    let uu____5948 =
                      let uu____5950 = FStar_Tactics_Types.goal_env g  in
                      let uu____6059 = FStar_Tactics_Types.goal_type g  in
                      tts uu____5950 uu____6059  in
                    FStar_Util.JsonStr uu____5948  in
                  ("type", uu____5947)  in
                [uu____5941;
                ("label", (FStar_Util.JsonStr (g.FStar_Tactics_Types.label)))]
                 in
              uu____5804 :: uu____5933  in
            FStar_Util.JsonAssoc uu____5796  in
          ("goal", uu____5795)  in
        [uu____5789]  in
      ("hyps", g_binders) :: uu____5781  in
    FStar_Util.JsonAssoc uu____5773
  
let (ps_to_json :
  (Prims.string * FStar_Tactics_Types.proofstate) -> FStar_Util.json) =
  fun uu____6188  ->
    match uu____6188 with
    | (msg,ps) ->
        let uu____6399 =
          let uu____6407 =
            let uu____6415 =
              let uu____6423 =
                let uu____6431 =
                  let uu____6437 =
                    let uu____6438 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____6438  in
                  ("goals", uu____6437)  in
                let uu____6502 =
                  let uu____6510 =
                    let uu____6516 =
                      let uu____6517 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____6517  in
                    ("smt-goals", uu____6516)  in
                  [uu____6510]  in
                uu____6431 :: uu____6502  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____6423
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____6415  in
          let uu____6610 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____6626 =
                let uu____6632 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____6632)  in
              [uu____6626]
            else []  in
          FStar_List.append uu____6407 uu____6610  in
        FStar_Util.JsonAssoc uu____6399
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____6806  ->
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
         (let uu____7048 = FStar_Tactics_Types.subst_proof_state subst1 ps
             in
          dump_proofstate uu____7048 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let traise : 'a . Prims.exn -> 'a tac =
  fun e  -> mk_tac (fun ps  -> FStar_Tactics_Result.Failed (e, ps)) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____7669 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____7669
          then dump_proofstate ps (Prims.op_Hat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed
           ((FStar_Tactics_Types.TacticFailure msg), ps))
  
let fail1 : 'Auu____7750 . Prims.string -> Prims.string -> 'Auu____7750 tac =
  fun msg  ->
    fun x  -> let uu____7770 = FStar_Util.format1 msg x  in fail uu____7770
  
let fail2 :
  'Auu____7781 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____7781 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        let uu____7808 = FStar_Util.format2 msg x y  in fail uu____7808
  
let fail3 :
  'Auu____7821 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____7821 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____7855 = FStar_Util.format3 msg x y z  in fail uu____7855
  
let fail4 :
  'Auu____7870 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____7870 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____7911 = FStar_Util.format4 msg x y z w  in
            fail uu____7911
  
let catch : 'a . 'a tac -> (Prims.exn,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____8019 = run t ps  in
         match uu____8019 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___183_8512 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___183_8512.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___183_8512.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___183_8512.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___183_8512.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___183_8512.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___183_8512.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___183_8512.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___183_8512.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___183_8512.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___183_8512.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___183_8512.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (uu___183_8512.FStar_Tactics_Types.local_state)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let recover : 'a . 'a tac -> (Prims.exn,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let uu____8825 = run t ps  in
         match uu____8825 with
         | FStar_Tactics_Result.Success (a,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inr a), q)
         | FStar_Tactics_Result.Failed (m,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inl m), q))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____9281 = catch t  in
    bind uu____9281
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____9314 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try
           (fun uu___209_9419  ->
              match () with
              | () -> let uu____9424 = trytac t  in run uu____9424 ps) ()
         with
         | FStar_Errors.Err (uu____9443,msg) ->
             (log ps
                (fun uu____9449  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____9522,msg,uu____9524) ->
             (log ps
                (fun uu____9529  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____9706 = run t ps  in
           match uu____9706 with
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
  fun p  -> mk_tac (fun uu____10473  -> FStar_Tactics_Result.Success ((), p)) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___244_10762 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___244_10762.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___244_10762.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___244_10762.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___244_10762.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___244_10762.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___244_10762.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___244_10762.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___244_10762.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___244_10762.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___244_10762.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___244_10762.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___244_10762.FStar_Tactics_Types.local_state)
            }))
  
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____11054 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____11054
         then
           let uu____11058 = FStar_Syntax_Print.term_to_string t1  in
           let uu____11060 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____11058
             uu____11060
         else ());
        (try
           (fun uu___252_11074  ->
              match () with
              | () ->
                  let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
                  ((let uu____11089 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____11089
                    then
                      let uu____11093 =
                        FStar_Common.string_of_option
                          (FStar_TypeChecker_Rel.guard_to_string env) res
                         in
                      let uu____11099 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____11101 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.print3
                        "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____11093
                        uu____11099 uu____11101
                    else ());
                   (match res with
                    | FStar_Pervasives_Native.None  -> ret false
                    | FStar_Pervasives_Native.Some g ->
                        let uu____11127 =
                          add_implicits g.FStar_TypeChecker_Env.implicits  in
                        bind uu____11127 (fun uu____11135  -> ret true)))) ()
         with
         | FStar_Errors.Err (uu____11148,msg) ->
             mlog
               (fun uu____11154  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____11157  -> ret false)
         | FStar_Errors.Error (uu____11160,msg,r) ->
             mlog
               (fun uu____11168  ->
                  let uu____11169 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____11169) (fun uu____11173  -> ret false))
  
let (compress_implicits : unit tac) =
  bind get
    (fun ps  ->
       let imps = ps.FStar_Tactics_Types.all_implicits  in
       let g =
         let uu___278_11332 = FStar_TypeChecker_Env.trivial_guard  in
         {
           FStar_TypeChecker_Env.guard_f =
             (uu___278_11332.FStar_TypeChecker_Env.guard_f);
           FStar_TypeChecker_Env.deferred =
             (uu___278_11332.FStar_TypeChecker_Env.deferred);
           FStar_TypeChecker_Env.univ_ineqs =
             (uu___278_11332.FStar_TypeChecker_Env.univ_ineqs);
           FStar_TypeChecker_Env.implicits = imps
         }  in
       let g1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g
          in
       let ps' =
         let uu___282_11485 = ps  in
         {
           FStar_Tactics_Types.main_context =
             (uu___282_11485.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___282_11485.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (g1.FStar_TypeChecker_Env.implicits);
           FStar_Tactics_Types.goals =
             (uu___282_11485.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___282_11485.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___282_11485.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___282_11485.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___282_11485.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___282_11485.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___282_11485.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___282_11485.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___282_11485.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___282_11485.FStar_Tactics_Types.local_state)
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
          (fun uu____11776  ->
             (let uu____11778 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____11778
              then
                (FStar_Options.push ();
                 (let uu____11783 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____11787 = __do_unify env t1 t2  in
              bind uu____11787
                (fun r  ->
                   (let uu____11801 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____11801 then FStar_Options.pop () else ());
                   ret r)))
  
let (remove_solved_goals : unit tac) =
  bind get
    (fun ps  ->
       let ps' =
         let uu___297_12086 = ps  in
         let uu____12221 =
           FStar_List.filter
             (fun g  ->
                let uu____12404 = check_goal_solved g  in
                FStar_Option.isNone uu____12404) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___297_12086.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___297_12086.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___297_12086.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____12221;
           FStar_Tactics_Types.smt_goals =
             (uu___297_12086.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___297_12086.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___297_12086.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___297_12086.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___297_12086.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___297_12086.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___297_12086.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___297_12086.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___297_12086.FStar_Tactics_Types.local_state)
         }  in
       set ps')
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____12562 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____12562 with
      | FStar_Pervasives_Native.Some uu____12574 ->
          let uu____12583 =
            let uu____12585 = goal_to_string_verbose goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____12585  in
          fail uu____12583
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____12742 = FStar_Tactics_Types.goal_env goal  in
      let uu____12851 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____12742 solution uu____12851
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____13003 =
         let uu___310_13138 = p  in
         let uu____13273 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___310_13138.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___310_13138.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___310_13138.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____13273;
           FStar_Tactics_Types.smt_goals =
             (uu___310_13138.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___310_13138.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___310_13138.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___310_13138.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___310_13138.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___310_13138.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___310_13138.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___310_13138.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___310_13138.FStar_Tactics_Types.local_state)
         }  in
       set uu____13003)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      mlog
        (fun uu____13653  ->
           let uu____13654 =
             let uu____13656 = FStar_Tactics_Types.goal_witness goal  in
             FStar_Syntax_Print.term_to_string uu____13656  in
           let uu____13665 = FStar_Syntax_Print.term_to_string solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____13654 uu____13665)
        (fun uu____13670  ->
           let uu____13671 = trysolve goal solution  in
           bind uu____13671
             (fun b  ->
                if b
                then bind __dismiss (fun uu____13689  -> remove_solved_goals)
                else
                  (let uu____13692 =
                     let uu____13694 =
                       let uu____13696 = FStar_Tactics_Types.goal_env goal
                          in
                       tts uu____13696 solution  in
                     let uu____13805 =
                       let uu____13807 = FStar_Tactics_Types.goal_env goal
                          in
                       let uu____13916 =
                         FStar_Tactics_Types.goal_witness goal  in
                       tts uu____13807 uu____13916  in
                     let uu____13925 =
                       let uu____13927 = FStar_Tactics_Types.goal_env goal
                          in
                       let uu____14036 = FStar_Tactics_Types.goal_type goal
                          in
                       tts uu____13927 uu____14036  in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____13694 uu____13805 uu____13925
                      in
                   fail uu____13692)))
  
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____14193 = set_solution goal solution  in
      bind uu____14193
        (fun uu____14200  ->
           bind __dismiss (fun uu____14202  -> remove_solved_goals))
  
let (set_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___326_14479 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___326_14479.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___326_14479.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___326_14479.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals = gs;
              FStar_Tactics_Types.smt_goals =
                (uu___326_14479.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___326_14479.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___326_14479.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___326_14479.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___326_14479.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___326_14479.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___326_14479.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___326_14479.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___326_14479.FStar_Tactics_Types.local_state)
            }))
  
let (set_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___330_14890 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___330_14890.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___330_14890.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___330_14890.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___330_14890.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals = gs;
              FStar_Tactics_Types.depth =
                (uu___330_14890.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___330_14890.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___330_14890.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___330_14890.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___330_14890.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___330_14890.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___330_14890.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___330_14890.FStar_Tactics_Types.local_state)
            }))
  
let (dismiss_all : unit tac) = set_goals [] 
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____15220 = FStar_Options.defensive ()  in
    if uu____15220
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____15338 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____15338)
         in
      let b2 =
        b1 &&
          (let uu____15350 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____15350)
         in
      let rec aux b3 e =
        let uu____15481 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____15481 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____15796 =
        (let uu____15800 = aux b2 env  in Prims.op_Negation uu____15800) &&
          (let uu____15803 = FStar_ST.op_Bang nwarn  in
           uu____15803 < (Prims.parse_int "5"))
         in
      (if uu____15796
       then
         ((let uu____15829 =
             let uu____15830 = FStar_Tactics_Types.goal_type g  in
             uu____15830.FStar_Syntax_Syntax.pos  in
           let uu____15841 =
             let uu____15847 =
               let uu____15849 = goal_to_string_verbose g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____15849
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____15847)  in
           FStar_Errors.log_issue uu____15829 uu____15841);
          (let uu____15853 =
             let uu____15855 = FStar_ST.op_Bang nwarn  in
             uu____15855 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____15853))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___352_16241 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___352_16241.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___352_16241.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___352_16241.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___352_16241.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___352_16241.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___352_16241.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___352_16241.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___352_16241.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___352_16241.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___352_16241.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___352_16241.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___352_16241.FStar_Tactics_Types.local_state)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___357_16772 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___357_16772.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___357_16772.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___357_16772.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___357_16772.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___357_16772.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___357_16772.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___357_16772.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___357_16772.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___357_16772.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___357_16772.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___357_16772.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___357_16772.FStar_Tactics_Types.local_state)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___362_17303 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___362_17303.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___362_17303.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___362_17303.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___362_17303.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___362_17303.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___362_17303.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___362_17303.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___362_17303.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___362_17303.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___362_17303.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___362_17303.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___362_17303.FStar_Tactics_Types.local_state)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___367_17834 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___367_17834.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___367_17834.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___367_17834.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___367_17834.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___367_17834.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___367_17834.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___367_17834.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___367_17834.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___367_17834.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___367_17834.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___367_17834.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___367_17834.FStar_Tactics_Types.local_state)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____18163  -> add_goals [g]) 
let (new_uvar :
  Prims.string ->
    env ->
      FStar_Reflection_Data.typ ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar) tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____18458 =
          FStar_TypeChecker_Env.new_implicit_var_aux reason
            typ.FStar_Syntax_Syntax.pos env typ
            FStar_Syntax_Syntax.Allow_untyped FStar_Pervasives_Native.None
           in
        match uu____18458 with
        | (u,ctx_uvar,g_u) ->
            let uu____18563 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____18563
              (fun uu____18587  ->
                 let uu____18588 =
                   let uu____18605 =
                     let uu____18622 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____18622  in
                   (u, uu____18605)  in
                 ret uu____18588)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____18707 = FStar_Syntax_Util.un_squash t1  in
    match uu____18707 with
    | FStar_Pervasives_Native.Some t' ->
        let t'1 = FStar_Syntax_Util.unascribe t'  in
        let uu____18739 =
          let uu____18740 = FStar_Syntax_Subst.compress t'1  in
          uu____18740.FStar_Syntax_Syntax.n  in
        (match uu____18739 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____18756 -> false)
    | uu____18758 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____18783 = FStar_Syntax_Util.un_squash t  in
    match uu____18783 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____18806 =
          let uu____18807 = FStar_Syntax_Subst.compress t'  in
          uu____18807.FStar_Syntax_Syntax.n  in
        (match uu____18806 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____18823 -> false)
    | uu____18825 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____18904  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____19528 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____19528 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____19672 = goal_to_string_verbose hd1  in
                    let uu____19674 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____19672 uu____19674);
                   ret hd1)))
  
let (tadmit_t : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____19760 =
      bind get
        (fun ps  ->
           let uu____19903 = cur_goal ()  in
           bind uu____19903
             (fun g  ->
                (let uu____20090 =
                   let uu____20091 = FStar_Tactics_Types.goal_type g  in
                   uu____20091.FStar_Syntax_Syntax.pos  in
                 let uu____20102 =
                   let uu____20108 =
                     let uu____20110 =
                       goal_to_string "" FStar_Pervasives_Native.None ps g
                        in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____20110
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____20108)  in
                 FStar_Errors.log_issue uu____20090 uu____20102);
                solve' g t))
       in
    FStar_All.pipe_left (wrap_err "tadmit_t") uu____19760
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____20142  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___412_20424 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___412_20424.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___412_20424.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___412_20424.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___412_20424.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___412_20424.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___412_20424.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___412_20424.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___412_20424.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___412_20424.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___412_20424.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___412_20424.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (uu___412_20424.FStar_Tactics_Types.local_state)
           }  in
         let uu____20560 = set ps1  in
         bind uu____20560
           (fun uu____20568  ->
              let uu____20569 = FStar_BigInt.of_int_fs n1  in ret uu____20569))
  
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
              let uu____20855 = env.FStar_TypeChecker_Env.universe_of env phi
                 in
              FStar_Syntax_Util.mk_squash uu____20855 phi  in
            let uu____20856 = new_uvar reason env typ  in
            bind uu____20856
              (fun uu____20957  ->
                 match uu____20957 with
                 | (uu____21038,ctx_uvar) ->
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
             (fun uu____21590  ->
                let uu____21591 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____21591)
             (fun uu____21596  ->
                let e1 =
                  let uu___430_21706 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___430_21706.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___430_21706.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___430_21706.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___430_21706.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___430_21706.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___430_21706.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___430_21706.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___430_21706.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___430_21706.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___430_21706.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___430_21706.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___430_21706.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___430_21706.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___430_21706.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___430_21706.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___430_21706.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___430_21706.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___430_21706.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___430_21706.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___430_21706.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___430_21706.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___430_21706.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___430_21706.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___430_21706.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___430_21706.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___430_21706.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___430_21706.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___430_21706.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___430_21706.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___430_21706.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___430_21706.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___430_21706.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___430_21706.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___430_21706.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___430_21706.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___430_21706.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___430_21706.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___430_21706.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___430_21706.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___430_21706.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___430_21706.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___430_21706.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___434_21841  ->
                     match () with
                     | () ->
                         let uu____21865 =
                           FStar_TypeChecker_TcTerm.type_of_tot_term e1 t  in
                         ret uu____21865) ()
                with
                | FStar_Errors.Err (uu____21931,msg) ->
                    let uu____21935 = tts e1 t  in
                    let uu____21937 =
                      let uu____21939 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____21939
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____21935 uu____21937 msg
                | FStar_Errors.Error (uu____21961,msg,uu____21963) ->
                    let uu____21966 = tts e1 t  in
                    let uu____21968 =
                      let uu____21970 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____21970
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____21966 uu____21968 msg))
  
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
             (fun uu____22339  ->
                let uu____22340 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc_ghost(%s)\n" uu____22340)
             (fun uu____22345  ->
                let e1 =
                  let uu___451_22455 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___451_22455.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___451_22455.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___451_22455.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___451_22455.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___451_22455.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___451_22455.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___451_22455.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___451_22455.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___451_22455.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___451_22455.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___451_22455.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___451_22455.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___451_22455.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___451_22455.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___451_22455.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___451_22455.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___451_22455.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___451_22455.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___451_22455.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___451_22455.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___451_22455.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___451_22455.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___451_22455.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___451_22455.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___451_22455.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___451_22455.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___451_22455.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___451_22455.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___451_22455.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___451_22455.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___451_22455.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___451_22455.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___451_22455.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___451_22455.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___451_22455.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___451_22455.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___451_22455.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___451_22455.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___451_22455.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___451_22455.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___451_22455.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___451_22455.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___455_22593  ->
                     match () with
                     | () ->
                         let uu____22617 =
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e1 t
                            in
                         (match uu____22617 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____22757,msg) ->
                    let uu____22761 = tts e1 t  in
                    let uu____22763 =
                      let uu____22765 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____22765
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____22761 uu____22763 msg
                | FStar_Errors.Error (uu____22787,msg,uu____22789) ->
                    let uu____22792 = tts e1 t  in
                    let uu____22794 =
                      let uu____22796 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____22796
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____22792 uu____22794 msg))
  
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
             (fun uu____23181  ->
                let uu____23182 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____23182)
             (fun uu____23188  ->
                let e1 =
                  let uu___476_23298 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___476_23298.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___476_23298.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___476_23298.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___476_23298.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___476_23298.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___476_23298.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___476_23298.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___476_23298.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___476_23298.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___476_23298.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___476_23298.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___476_23298.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___476_23298.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___476_23298.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___476_23298.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___476_23298.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___476_23298.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___476_23298.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___476_23298.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___476_23298.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___476_23298.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___476_23298.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___476_23298.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___476_23298.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___476_23298.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___476_23298.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___476_23298.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___476_23298.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___476_23298.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___476_23298.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___476_23298.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___476_23298.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___476_23298.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___476_23298.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___476_23298.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___476_23298.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___476_23298.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___476_23298.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___476_23298.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___476_23298.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___476_23298.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___476_23298.FStar_TypeChecker_Env.nbe)
                  }  in
                let e2 =
                  let uu___479_23517 = e1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___479_23517.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___479_23517.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___479_23517.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___479_23517.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___479_23517.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___479_23517.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___479_23517.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___479_23517.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___479_23517.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___479_23517.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___479_23517.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___479_23517.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___479_23517.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___479_23517.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___479_23517.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___479_23517.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___479_23517.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___479_23517.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___479_23517.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___479_23517.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___479_23517.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___479_23517.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___479_23517.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___479_23517.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___479_23517.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___479_23517.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___479_23517.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___479_23517.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___479_23517.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___479_23517.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___479_23517.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___479_23517.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___479_23517.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___479_23517.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___479_23517.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___479_23517.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___479_23517.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___479_23517.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___479_23517.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___479_23517.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___479_23517.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___479_23517.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___483_23656  ->
                     match () with
                     | () ->
                         let uu____23684 =
                           FStar_TypeChecker_TcTerm.tc_term e2 t  in
                         ret uu____23684) ()
                with
                | FStar_Errors.Err (uu____23762,msg) ->
                    let uu____23766 = tts e2 t  in
                    let uu____23768 =
                      let uu____23770 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____23770
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____23766 uu____23768 msg
                | FStar_Errors.Error (uu____23796,msg,uu____23798) ->
                    let uu____23801 = tts e2 t  in
                    let uu____23803 =
                      let uu____23805 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____23805
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____23801 uu____23803 msg))
  
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
  fun uu____23982  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___504_24278 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___504_24278.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___504_24278.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___504_24278.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___504_24278.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___504_24278.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___504_24278.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___504_24278.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___504_24278.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___504_24278.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___504_24278.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___504_24278.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___504_24278.FStar_Tactics_Types.local_state)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____24443 = get_guard_policy ()  in
      bind uu____24443
        (fun old_pol  ->
           let uu____24452 = set_guard_policy pol  in
           bind uu____24452
             (fun uu____24459  ->
                bind t
                  (fun r  ->
                     let uu____24463 = set_guard_policy old_pol  in
                     bind uu____24463 (fun uu____24470  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____24477 = let uu____24544 = cur_goal ()  in trytac uu____24544  in
  bind uu____24477
    (fun uu___0_24731  ->
       match uu___0_24731 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____24976 = FStar_Options.peek ()  in ret uu____24976)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        mlog
          (fun uu____25123  ->
             let uu____25124 = FStar_TypeChecker_Rel.guard_to_string e g  in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason
               uu____25124)
          (fun uu____25129  ->
             let uu____25130 =
               add_implicits g.FStar_TypeChecker_Env.implicits  in
             bind uu____25130
               (fun uu____25137  ->
                  bind getopts
                    (fun opts  ->
                       let uu____25141 =
                         let uu____25142 =
                           FStar_TypeChecker_Rel.simplify_guard e g  in
                         uu____25142.FStar_TypeChecker_Env.guard_f  in
                       match uu____25141 with
                       | FStar_TypeChecker_Common.Trivial  -> ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____25161 = istrivial e f  in
                           if uu____25161
                           then ret ()
                           else
                             bind get
                               (fun ps  ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop  ->
                                      ((let uu____25314 =
                                          let uu____25320 =
                                            let uu____25322 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g
                                               in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____25322
                                             in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____25320)
                                           in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____25314);
                                       ret ())
                                  | FStar_Tactics_Types.Goal  ->
                                      mlog
                                        (fun uu____25328  ->
                                           let uu____25329 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____25329)
                                        (fun uu____25334  ->
                                           let uu____25335 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____25335
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___533_25641 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___533_25641.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___533_25641.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___533_25641.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___533_25641.FStar_Tactics_Types.label)
                                                  }  in
                                                push_goals [goal1]))
                                  | FStar_Tactics_Types.SMT  ->
                                      mlog
                                        (fun uu____25881  ->
                                           let uu____25882 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____25882)
                                        (fun uu____25887  ->
                                           let uu____25888 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____25888
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___540_26194 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___540_26194.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___540_26194.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___540_26194.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___540_26194.FStar_Tactics_Types.label)
                                                  }  in
                                                push_smt_goals [goal1]))
                                  | FStar_Tactics_Types.Force  ->
                                      mlog
                                        (fun uu____26434  ->
                                           let uu____26435 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____26435)
                                        (fun uu____26439  ->
                                           try
                                             (fun uu___547_26447  ->
                                                match () with
                                                | () ->
                                                    let uu____26453 =
                                                      let uu____26455 =
                                                        let uu____26457 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____26457
                                                         in
                                                      Prims.op_Negation
                                                        uu____26455
                                                       in
                                                    if uu____26453
                                                    then
                                                      mlog
                                                        (fun uu____26479  ->
                                                           let uu____26480 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g
                                                              in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____26480)
                                                        (fun uu____26484  ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else ret ()) ()
                                           with
                                           | uu___546_26489 ->
                                               mlog
                                                 (fun uu____26497  ->
                                                    let uu____26498 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g
                                                       in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____26498)
                                                 (fun uu____26502  ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
  
let (tcc : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp tac) =
  fun t  ->
    let uu____26536 =
      let uu____26546 = cur_goal ()  in
      bind uu____26546
        (fun goal  ->
           let uu____26736 =
             let uu____26764 = FStar_Tactics_Types.goal_env goal  in
             __tc_lax uu____26764 t  in
           bind uu____26736
             (fun uu____26904  ->
                match uu____26904 with
                | (uu____26936,lc,uu____26938) ->
                    let uu____26971 = FStar_Syntax_Syntax.lcomp_comp lc  in
                    ret uu____26971))
       in
    FStar_All.pipe_left (wrap_err "tcc") uu____26536
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____27039 =
      let uu____27051 = tcc t  in
      bind uu____27051 (fun c  -> ret (FStar_Syntax_Util.comp_result c))  in
    FStar_All.pipe_left (wrap_err "tc") uu____27039
  
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
            let uu____27266 = mk_irrelevant_goal reason env phi opts label1
               in
            bind uu____27266 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____27579  ->
    let uu____27585 = cur_goal ()  in
    bind uu____27585
      (fun goal  ->
         let uu____27771 =
           let uu____27773 = FStar_Tactics_Types.goal_env goal  in
           let uu____27882 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____27773 uu____27882  in
         if uu____27771
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____27899 =
              let uu____27901 = FStar_Tactics_Types.goal_env goal  in
              let uu____28010 = FStar_Tactics_Types.goal_type goal  in
              tts uu____27901 uu____28010  in
            fail1 "Not a trivial goal: %s" uu____27899))
  
let divide : 'a 'b . FStar_BigInt.t -> 'a tac -> 'b tac -> ('a * 'b) tac =
  fun n1  ->
    fun l  ->
      fun r  ->
        bind get
          (fun p  ->
             let uu____28212 =
               try
                 (fun uu___605_28477  ->
                    match () with
                    | () ->
                        let uu____28609 =
                          let uu____28736 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____28736
                            p.FStar_Tactics_Types.goals
                           in
                        ret uu____28609) ()
               with | uu___604_28924 -> fail "divide: not enough goals"  in
             bind uu____28212
               (fun uu____29318  ->
                  match uu____29318 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___587_29835 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___587_29835.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___587_29835.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___587_29835.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___587_29835.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___587_29835.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___587_29835.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___587_29835.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___587_29835.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___587_29835.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___587_29835.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___587_29835.FStar_Tactics_Types.local_state)
                        }  in
                      let uu____30029 = set lp  in
                      bind uu____30029
                        (fun uu____30040  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___593_30324 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___593_30324.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___593_30324.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___593_30324.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___593_30324.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___593_30324.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___593_30324.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___593_30324.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___593_30324.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___593_30324.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___593_30324.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___593_30324.FStar_Tactics_Types.local_state)
                                       }  in
                                     let uu____30518 = set rp  in
                                     bind uu____30518
                                       (fun uu____30529  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___599_30813 =
                                                        rp'  in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___599_30813.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___599_30813.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___599_30813.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___599_30813.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___599_30813.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___599_30813.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___599_30813.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___599_30813.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___599_30813.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___599_30813.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___599_30813.FStar_Tactics_Types.local_state)
                                                      }  in
                                                    let uu____31125 = set p'
                                                       in
                                                    bind uu____31125
                                                      (fun uu____31136  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____31142 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____31170 = divide FStar_BigInt.one f idtac  in
    bind uu____31170
      (fun uu____31186  -> match uu____31186 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____31429::uu____31430 ->
             let uu____31610 =
               let uu____31622 = map tau  in
               divide FStar_BigInt.one tau uu____31622  in
             bind uu____31610
               (fun uu____31643  ->
                  match uu____31643 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____31700 =
        bind t1
          (fun uu____31708  ->
             let uu____31709 = map t2  in
             bind uu____31709 (fun uu____31720  -> ret ()))
         in
      focus uu____31700
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____31733  ->
    let uu____31739 =
      let uu____31745 = cur_goal ()  in
      bind uu____31745
        (fun goal  ->
           let uu____31934 =
             let uu____31945 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____31945  in
           match uu____31934 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____31977 =
                 let uu____31979 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____31979  in
               if uu____31977
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____32099 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____32099 [b]  in
                  let typ' = FStar_Syntax_Util.comp_result c  in
                  let uu____32241 = new_uvar "intro" env' typ'  in
                  bind uu____32241
                    (fun uu____32285  ->
                       match uu____32285 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c))
                              in
                           let uu____32373 = set_solution goal sol  in
                           bind uu____32373
                             (fun uu____32382  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                    goal.FStar_Tactics_Types.label
                                   in
                                let uu____32502 =
                                  let uu____32508 = bnorm_goal g  in
                                  replace_cur uu____32508  in
                                bind uu____32502 (fun uu____32628  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____32637 =
                 let uu____32639 = FStar_Tactics_Types.goal_env goal  in
                 let uu____32748 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____32639 uu____32748  in
               fail1 "goal is not an arrow (%s)" uu____32637)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____31739
  
let (intro_rec :
  unit -> (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder) tac) =
  fun uu____32783  ->
    let uu____32793 = cur_goal ()  in
    bind uu____32793
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____32992 =
            let uu____33003 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____33003  in
          match uu____32992 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____33039 =
                let uu____33041 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____33041  in
              if uu____33039
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____33071 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____33071
                    in
                 let bs =
                   let uu____33095 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____33095; b]  in
                 let env' =
                   let uu____33249 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____33249 bs  in
                 let uu____33358 =
                   new_uvar "intro_rec" env'
                     (FStar_Syntax_Util.comp_result c)
                    in
                 bind uu____33358
                   (fun uu____33411  ->
                      match uu____33411 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____33478 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____33489 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____33478
                              FStar_Parser_Const.effect_Tot_lid uu____33489
                              [] FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____33554 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____33554 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____33634 =
                                   let uu____33635 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____33635.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____33634
                                  in
                               let uu____33677 = set_solution goal tm  in
                               bind uu____33677
                                 (fun uu____33689  ->
                                    let uu____33690 =
                                      let uu____33696 =
                                        bnorm_goal
                                          (let uu___670_33817 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___670_33817.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___670_33817.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___670_33817.FStar_Tactics_Types.is_guard);
                                             FStar_Tactics_Types.label =
                                               (uu___670_33817.FStar_Tactics_Types.label)
                                           })
                                         in
                                      replace_cur uu____33696  in
                                    bind uu____33690
                                      (fun uu____33942  ->
                                         let uu____33943 =
                                           let uu____33948 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____33948, b)  in
                                         ret uu____33943)))))
          | FStar_Pervasives_Native.None  ->
              let uu____33961 =
                let uu____33963 = FStar_Tactics_Types.goal_env goal  in
                let uu____34072 = FStar_Tactics_Types.goal_type goal  in
                tts uu____33963 uu____34072  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____33961))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____34106 = cur_goal ()  in
    bind uu____34106
      (fun goal  ->
         mlog
           (fun uu____34293  ->
              let uu____34294 =
                let uu____34296 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____34296  in
              FStar_Util.print1 "norm: witness = %s\n" uu____34294)
           (fun uu____34310  ->
              let steps =
                let uu____34314 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____34314
                 in
              let t =
                let uu____34326 = FStar_Tactics_Types.goal_env goal  in
                let uu____34435 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____34326 uu____34435  in
              let uu____34444 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____34444))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____34717 =
          bind get
            (fun ps  ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
                 | g::uu____34870 -> g.FStar_Tactics_Types.opts
                 | uu____35050 -> FStar_Options.peek ()  in
               mlog
                 (fun uu____35118  ->
                    let uu____35119 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____35119)
                 (fun uu____35124  ->
                    let uu____35125 = __tc_lax e t  in
                    bind uu____35125
                      (fun uu____35185  ->
                         match uu____35185 with
                         | (t1,uu____35218,uu____35219) ->
                             let steps =
                               let uu____35255 =
                                 FStar_TypeChecker_Normalize.tr_norm_steps s
                                  in
                               FStar_List.append
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu____35255
                                in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1
                                in
                             mlog
                               (fun uu____35273  ->
                                  let uu____35274 =
                                    FStar_Syntax_Print.term_to_string t2  in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____35274)
                               (fun uu____35278  -> ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____34717
  
let (refine_intro : unit -> unit tac) =
  fun uu____35316  ->
    let uu____35322 =
      let uu____35328 = cur_goal ()  in
      bind uu____35328
        (fun g  ->
           let uu____35515 =
             let uu____35539 = FStar_Tactics_Types.goal_env g  in
             let uu____35648 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____35539
               uu____35648
              in
           match uu____35515 with
           | (uu____35662,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____35876 =
                 let uu____35890 =
                   let uu____35899 =
                     let uu____35900 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____35900]  in
                   FStar_Syntax_Subst.open_term uu____35899 phi  in
                 match uu____35890 with
                 | (bvs,phi1) ->
                     let uu____35957 =
                       let uu____35968 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____35968  in
                     (uu____35957, phi1)
                  in
               (match uu____35876 with
                | (bv1,phi1) ->
                    let uu____36032 =
                      let uu____36097 = FStar_Tactics_Types.goal_env g  in
                      let uu____36206 =
                        let uu____36215 =
                          let uu____36218 =
                            let uu____36219 =
                              let uu____36235 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____36235)  in
                            FStar_Syntax_Syntax.NT uu____36219  in
                          [uu____36218]  in
                        FStar_Syntax_Subst.subst uu____36215 phi1  in
                      mk_irrelevant_goal "refine_intro refinement"
                        uu____36097 uu____36206 g.FStar_Tactics_Types.opts
                        g.FStar_Tactics_Types.label
                       in
                    bind uu____36032
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____36379  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____35322
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____36599 = cur_goal ()  in
      bind uu____36599
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____36950 = FStar_Tactics_Types.goal_env goal  in
               let uu____37059 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____36950 uu____37059
             else FStar_Tactics_Types.goal_env goal  in
           let uu____37070 = __tc env t  in
           bind uu____37070
             (fun uu____37116  ->
                match uu____37116 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____37170  ->
                         let uu____37171 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____37173 =
                           let uu____37175 =
                             FStar_Tactics_Types.goal_env goal  in
                           FStar_TypeChecker_Rel.guard_to_string uu____37175
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____37171 uu____37173)
                      (fun uu____37287  ->
                         let uu____37288 =
                           let uu____37294 =
                             FStar_Tactics_Types.goal_env goal  in
                           proc_guard "__exact typing" uu____37294 guard  in
                         bind uu____37288
                           (fun uu____37405  ->
                              mlog
                                (fun uu____37409  ->
                                   let uu____37410 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____37412 =
                                     let uu____37414 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____37414
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____37410 uu____37412)
                                (fun uu____37426  ->
                                   let uu____37427 =
                                     let uu____37434 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____37543 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____37434 typ uu____37543  in
                                   bind uu____37427
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____37564 =
                                             let uu____37566 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____37566 t1  in
                                           let uu____37675 =
                                             let uu____37677 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____37677 typ  in
                                           let uu____37786 =
                                             let uu____37788 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____37897 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____37788 uu____37897  in
                                           let uu____37906 =
                                             let uu____37908 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____38017 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____37908 uu____38017  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____37564 uu____37675
                                             uu____37786 uu____37906)))))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun try_refine  ->
    fun set_expected_typ1  ->
      fun tm  ->
        let uu____38065 =
          mlog
            (fun uu____38073  ->
               let uu____38074 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____38074)
            (fun uu____38079  ->
               let uu____38080 =
                 let uu____38090 = __exact_now set_expected_typ1 tm  in
                 catch uu____38090  in
               bind uu____38080
                 (fun uu___2_38102  ->
                    match uu___2_38102 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        traise e
                    | FStar_Util.Inl e ->
                        mlog
                          (fun uu____38116  ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____38120  ->
                             let uu____38121 =
                               let uu____38131 =
                                 let uu____38137 =
                                   norm [FStar_Syntax_Embeddings.Delta]  in
                                 bind uu____38137
                                   (fun uu____38145  ->
                                      let uu____38146 = refine_intro ()  in
                                      bind uu____38146
                                        (fun uu____38153  ->
                                           __exact_now set_expected_typ1 tm))
                                  in
                               catch uu____38131  in
                             bind uu____38121
                               (fun uu___1_38160  ->
                                  match uu___1_38160 with
                                  | FStar_Util.Inr r ->
                                      mlog
                                        (fun uu____38172  ->
                                           FStar_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu____38175  -> ret ())
                                  | FStar_Util.Inl uu____38176 ->
                                      mlog
                                        (fun uu____38178  ->
                                           FStar_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu____38181  -> traise e)))))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____38065
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____38245 = f x  in
          bind uu____38245
            (fun y  ->
               let uu____38256 = mapM f xs  in
               bind uu____38256 (fun ys  -> ret (y :: ys)))
  
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
          let uu____38509 = do_unify e ty1 ty2  in
          bind uu____38509
            (fun uu___3_38538  ->
               if uu___3_38538
               then ret acc
               else
                 (let uu____38585 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____38585 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____38629 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____38631 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____38629
                        uu____38631
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____38672 =
                        let uu____38674 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____38674  in
                      if uu____38672
                      then fail "Codomain is effectful"
                      else
                        (let uu____38725 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____38725
                           (fun uu____38796  ->
                              match uu____38796 with
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
      let uu____39178 =
        mlog
          (fun uu____39186  ->
             let uu____39187 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_apply: tm = %s\n" uu____39187)
          (fun uu____39192  ->
             let uu____39193 = cur_goal ()  in
             bind uu____39193
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____39489 = __tc e tm  in
                  bind uu____39489
                    (fun uu____39537  ->
                       match uu____39537 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____39597 =
                             let uu____39623 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____39623  in
                           bind uu____39597
                             (fun uvs  ->
                                let fix_qual q =
                                  match q with
                                  | FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Meta uu____39693)
                                      ->
                                      FStar_Pervasives_Native.Some
                                        (FStar_Syntax_Syntax.Implicit false)
                                  | uu____39701 -> q  in
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____39748  ->
                                       fun w  ->
                                         match uu____39748 with
                                         | (uvt,q,uu____39786) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, (fix_qual q))]) uvs tm1
                                   in
                                let uvset =
                                  let uu____39862 =
                                    FStar_Syntax_Free.new_uv_set ()  in
                                  FStar_List.fold_right
                                    (fun uu____39907  ->
                                       fun s  ->
                                         match uu____39907 with
                                         | (uu____39947,uu____39948,uv) ->
                                             let uu____39974 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                in
                                             FStar_Util.set_union s
                                               uu____39974) uvs uu____39862
                                   in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset  in
                                let uu____40024 = solve' goal w  in
                                bind uu____40024
                                  (fun uu____40032  ->
                                     let uu____40033 =
                                       mapM
                                         (fun uu____40065  ->
                                            match uu____40065 with
                                            | (uvt,q,uv) ->
                                                let uu____40116 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                   in
                                                (match uu____40116 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____40128 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____40141 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv)
                                                        in
                                                     if uu____40141
                                                     then ret ()
                                                     else
                                                       (let uu____40151 =
                                                          let uu____40213 =
                                                            bnorm_goal
                                                              (let uu___831_40334
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___831_40334.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___831_40334.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false;
                                                                 FStar_Tactics_Types.label
                                                                   =
                                                                   (uu___831_40334.FStar_Tactics_Types.label)
                                                               })
                                                             in
                                                          [uu____40213]  in
                                                        add_goals uu____40151)))
                                         uvs
                                        in
                                     bind uu____40033
                                       (fun uu____40575  ->
                                          proc_guard "apply guard" e guard))))))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____39178
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____40643 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____40643
    then
      let uu____40660 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____40691 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____40780 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____40660 with
      | (pre,post) ->
          let post1 =
            let uu____40857 =
              let uu____40872 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____40872]  in
            FStar_Syntax_Util.mk_app post uu____40857  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____40931 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____40931
       then
         let uu____40948 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____40948
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
            let uu____41069 = f x e  in
            bind uu____41069 (fun e'  -> fold_left f e' xs1)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____41101 =
      let uu____41107 =
        bind get
          (fun ps  ->
             mlog
               (fun uu____41251  ->
                  let uu____41252 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____41252)
               (fun uu____41258  ->
                  let is_unit_t t =
                    let uu____41274 =
                      let uu____41275 = FStar_Syntax_Subst.compress t  in
                      uu____41275.FStar_Syntax_Syntax.n  in
                    match uu____41274 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____41292 -> false  in
                  let uu____41294 = cur_goal ()  in
                  bind uu____41294
                    (fun goal  ->
                       let uu____41480 =
                         let uu____41504 = FStar_Tactics_Types.goal_env goal
                            in
                         __tc uu____41504 tm  in
                       bind uu____41480
                         (fun uu____41639  ->
                            match uu____41639 with
                            | (tm1,t,guard) ->
                                let uu____41690 =
                                  FStar_Syntax_Util.arrow_formals_comp t  in
                                (match uu____41690 with
                                 | (bs,comp) ->
                                     let uu____41753 = lemma_or_sq comp  in
                                     (match uu____41753 with
                                      | FStar_Pervasives_Native.None  ->
                                          fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre,post) ->
                                          let uu____41816 =
                                            fold_left
                                              (fun uu____41918  ->
                                                 fun uu____41919  ->
                                                   match (uu____41918,
                                                           uu____41919)
                                                   with
                                                   | ((b,aq),(uvs,imps,subst1))
                                                       ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst1
                                                           b.FStar_Syntax_Syntax.sort
                                                          in
                                                       let uu____42202 =
                                                         is_unit_t b_t  in
                                                       if uu____42202
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
                                                         (let uu____42428 =
                                                            let uu____42450 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            new_uvar
                                                              "apply_lemma"
                                                              uu____42450 b_t
                                                             in
                                                          bind uu____42428
                                                            (fun uu____42617 
                                                               ->
                                                               match uu____42617
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
                                          bind uu____41816
                                            (fun uu____43014  ->
                                               match uu____43014 with
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
                                                   let uu____43201 =
                                                     let uu____43208 =
                                                       FStar_Tactics_Types.goal_env
                                                         goal
                                                        in
                                                     let uu____43317 =
                                                       FStar_Syntax_Util.mk_squash
                                                         FStar_Syntax_Syntax.U_zero
                                                         post1
                                                        in
                                                     let uu____43326 =
                                                       FStar_Tactics_Types.goal_type
                                                         goal
                                                        in
                                                     do_unify uu____43208
                                                       uu____43317
                                                       uu____43326
                                                      in
                                                   bind uu____43201
                                                     (fun b  ->
                                                        if
                                                          Prims.op_Negation b
                                                        then
                                                          let uu____43348 =
                                                            let uu____43350 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            tts uu____43350
                                                              tm1
                                                             in
                                                          let uu____43459 =
                                                            let uu____43461 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            let uu____43570 =
                                                              FStar_Syntax_Util.mk_squash
                                                                FStar_Syntax_Syntax.U_zero
                                                                post1
                                                               in
                                                            tts uu____43461
                                                              uu____43570
                                                             in
                                                          let uu____43579 =
                                                            let uu____43581 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            let uu____43690 =
                                                              FStar_Tactics_Types.goal_type
                                                                goal
                                                               in
                                                            tts uu____43581
                                                              uu____43690
                                                             in
                                                          fail3
                                                            "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                            uu____43348
                                                            uu____43459
                                                            uu____43579
                                                        else
                                                          (let uu____43702 =
                                                             solve' goal
                                                               FStar_Syntax_Util.exp_unit
                                                              in
                                                           bind uu____43702
                                                             (fun uu____43713
                                                                 ->
                                                                let is_free_uvar
                                                                  uv t1 =
                                                                  let free_uvars
                                                                    =
                                                                    let uu____43753
                                                                    =
                                                                    let uu____43764
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____43764
                                                                     in
                                                                    FStar_List.map
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____43753
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
                                                                    let uu____44074
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____44074)
                                                                    goals
                                                                   in
                                                                let checkone
                                                                  t1 goals =
                                                                  let uu____44225
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                  match uu____44225
                                                                  with
                                                                  | (hd1,uu____44252)
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____44295)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____44328
                                                                    -> false)
                                                                   in
                                                                let uu____44330
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
                                                                    let uu____44592
                                                                    = imp  in
                                                                    match uu____44592
                                                                    with
                                                                    | 
                                                                    (term,ctx_uvar)
                                                                    ->
                                                                    let uu____44701
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____44701
                                                                    with
                                                                    | 
                                                                    (hd1,uu____44793)
                                                                    ->
                                                                    let uu____44834
                                                                    =
                                                                    let uu____44835
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____44835.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____44834
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____44913)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___941_45067
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___941_45067.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___941_45067.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___941_45067.FStar_Tactics_Types.is_guard);
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___941_45067.FStar_Tactics_Types.label)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____45365
                                                                    ->
                                                                    mlog
                                                                    (fun
                                                                    uu____45430
                                                                     ->
                                                                    let uu____45431
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                                                     in
                                                                    let uu____45433
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____45431
                                                                    uu____45433)
                                                                    (fun
                                                                    uu____45440
                                                                     ->
                                                                    let env =
                                                                    let uu___946_45550
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___946_45550.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___946_45550.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___946_45550.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___946_45550.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___946_45550.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___946_45550.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___946_45550.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___946_45550.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___946_45550.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___946_45550.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___946_45550.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___946_45550.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___946_45550.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___946_45550.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___946_45550.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___946_45550.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___946_45550.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___946_45550.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___946_45550.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___946_45550.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___946_45550.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___946_45550.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___946_45550.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___946_45550.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___946_45550.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___946_45550.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___946_45550.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___946_45550.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___946_45550.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___946_45550.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___946_45550.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___946_45550.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___946_45550.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___946_45550.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___946_45550.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___946_45550.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___946_45550.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___946_45550.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___946_45550.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___946_45550.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___946_45550.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___946_45550.FStar_TypeChecker_Env.nbe)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let uu____45669
                                                                    =
                                                                    let uu____45675
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____45679
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
                                                                    let uu____45681
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____45679
                                                                    uu____45681
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____45687
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    uu____45675
                                                                    uu____45687
                                                                    g_typ  in
                                                                    bind
                                                                    uu____45669
                                                                    (fun
                                                                    uu____45858
                                                                     ->
                                                                    ret []))))))
                                                                   in
                                                                bind
                                                                  uu____44330
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
                                                                    let uu____46276
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____46276
                                                                    then
                                                                    let uu____46281
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____46281
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
                                                                    let uu____46532
                                                                    =
                                                                    let uu____46534
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____46534
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____46532)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____46543
                                                                    =
                                                                    let uu____46549
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____46549
                                                                    guard  in
                                                                    bind
                                                                    uu____46543
                                                                    (fun
                                                                    uu____46661
                                                                     ->
                                                                    let uu____46662
                                                                    =
                                                                    let uu____46668
                                                                    =
                                                                    let uu____46670
                                                                    =
                                                                    let uu____46672
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____46781
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____46672
                                                                    uu____46781
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____46670
                                                                     in
                                                                    if
                                                                    uu____46668
                                                                    then
                                                                    let uu____46796
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____46796
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    goal.FStar_Tactics_Types.label
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____46662
                                                                    (fun
                                                                    uu____46909
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2)))))))))))))
         in
      focus uu____41107  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____41101
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____46963 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____46963 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____46981::(e1,uu____46983)::(e2,uu____46985)::[])) when
        (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) ||
          (FStar_Ident.lid_equals l FStar_Parser_Const.c_eq2_lid)
        -> FStar_Pervasives_Native.Some (e1, e2)
    | uu____47106 ->
        let uu____47109 = FStar_Syntax_Util.unb2t typ  in
        (match uu____47109 with
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some t ->
             ((let uu____47156 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "GG t = %s\n" uu____47156);
              (let uu____47159 = FStar_Syntax_Util.head_and_args t  in
               match uu____47159 with
               | (hd1,args) ->
                   let uu____47240 =
                     let uu____47259 =
                       let uu____47260 = FStar_Syntax_Subst.compress hd1  in
                       uu____47260.FStar_Syntax_Syntax.n  in
                     (uu____47259, args)  in
                   (match uu____47240 with
                    | (FStar_Syntax_Syntax.Tm_fvar
                       fv,(uu____47300,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit uu____47301))::
                       (e1,FStar_Pervasives_Native.None )::(e2,FStar_Pervasives_Native.None
                                                            )::[])
                        when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.op_Eq
                        ->
                        ((let uu____47413 =
                            FStar_Syntax_Print.term_to_string e1  in
                          let uu____47415 =
                            FStar_Syntax_Print.term_to_string e2  in
                          FStar_Util.print2 "wat %s -- %s\n" uu____47413
                            uu____47415);
                         FStar_Pervasives_Native.Some (e1, e2))
                    | uu____47438 -> FStar_Pervasives_Native.None))))
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____47511 = destruct_eq' typ  in
    match uu____47511 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____47589 = FStar_Syntax_Util.un_squash typ  in
        (match uu____47589 with
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
        let uu____48108 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____48108 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', bv', [])
            else
              (let uu____48786 = aux e'  in
               FStar_Util.map_opt uu____48786
                 (fun uu____49009  ->
                    match uu____49009 with
                    | (e'',bv,bvs) -> (e'', bv, (bv' :: bvs))))
         in
      let uu____49360 = aux e  in
      FStar_Util.map_opt uu____49360
        (fun uu____49583  ->
           match uu____49583 with
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
          let uu____50528 =
            let uu____50603 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____50603  in
          FStar_Util.map_opt uu____50528
            (fun uu____50852  ->
               match uu____50852 with
               | (e0,b11,bvs) ->
                   let s1 bv =
                     let uu___1043_51140 = bv  in
                     let uu____51151 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___1043_51140.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___1043_51140.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____51151
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___1047_51311 =
                       g.FStar_Tactics_Types.goal_ctx_uvar  in
                     let uu____51328 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____51342 =
                       let uu____51353 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____51353  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___1047_51311.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____51328;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____51342;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___1047_51311.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___1047_51311.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___1047_51311.FStar_Syntax_Syntax.ctx_uvar_range);
                       FStar_Syntax_Syntax.ctx_uvar_meta =
                         (uu___1047_51311.FStar_Syntax_Syntax.ctx_uvar_meta)
                     }  in
                   let uu___1050_51362 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1050_51362.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___1050_51362.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___1050_51362.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1050_51362.FStar_Tactics_Types.label)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____51497 =
      let uu____51503 = cur_goal ()  in
      bind uu____51503
        (fun goal  ->
           let uu____51691 = h  in
           match uu____51691 with
           | (bv,uu____51698) ->
               mlog
                 (fun uu____51716  ->
                    let uu____51717 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____51719 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____51717
                      uu____51719)
                 (fun uu____51724  ->
                    let uu____51725 =
                      let uu____51800 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____51800  in
                    match uu____51725 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                        let uu____52194 =
                          destruct_eq bv1.FStar_Syntax_Syntax.sort  in
                        (match uu____52194 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____52244 =
                               let uu____52245 =
                                 FStar_Syntax_Subst.compress x  in
                               uu____52245.FStar_Syntax_Syntax.n  in
                             (match uu____52244 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv2 =
                                    let uu___1073_52302 = bv2  in
                                    let uu____52313 =
                                      FStar_Syntax_Subst.subst s
                                        bv2.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1073_52302.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1073_52302.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____52313
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv1 :: bvs1)  in
                                  let new_goal =
                                    let uu___1077_52473 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____52490 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____52504 =
                                      let uu____52515 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____52515
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___1077_52473.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____52490;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____52504;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___1077_52473.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___1077_52473.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___1077_52473.FStar_Syntax_Syntax.ctx_uvar_range);
                                      FStar_Syntax_Syntax.ctx_uvar_meta =
                                        (uu___1077_52473.FStar_Syntax_Syntax.ctx_uvar_meta)
                                    }  in
                                  replace_cur
                                    (let uu___1080_52526 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___1080_52526.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___1080_52526.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___1080_52526.FStar_Tactics_Types.is_guard);
                                       FStar_Tactics_Types.label =
                                         (uu___1080_52526.FStar_Tactics_Types.label)
                                     })
                              | uu____52645 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____52647 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____51497
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____52697 =
        let uu____52703 = cur_goal ()  in
        bind uu____52703
          (fun goal  ->
             let uu____52894 = b  in
             match uu____52894 with
             | (bv,uu____52901) ->
                 let bv' =
                   let uu____52927 =
                     let uu___1091_52938 = bv  in
                     let uu____52949 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____52949;
                       FStar_Syntax_Syntax.index =
                         (uu___1091_52938.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___1091_52938.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____52927  in
                 let s1 =
                   let uu____52958 =
                     let uu____52959 =
                       let uu____52975 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____52975)  in
                     FStar_Syntax_Syntax.NT uu____52959  in
                   [uu____52958]  in
                 let uu____52997 = subst_goal bv bv' s1 goal  in
                 (match uu____52997 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____52697
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____53270 =
      let uu____53276 = cur_goal ()  in
      bind uu____53276
        (fun goal  ->
           let uu____53465 = b  in
           match uu____53465 with
           | (bv,uu____53472) ->
               let uu____53487 =
                 let uu____53562 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____53562  in
               (match uu____53487 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                    let uu____53956 = FStar_Syntax_Util.type_u ()  in
                    (match uu____53956 with
                     | (ty,u) ->
                         let uu____53980 = new_uvar "binder_retype" e0 ty  in
                         bind uu____53980
                           (fun uu____54026  ->
                              match uu____54026 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___1115_54085 = bv1  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1115_54085.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1115_54085.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____54099 =
                                      let uu____54100 =
                                        let uu____54116 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv1, uu____54116)  in
                                      FStar_Syntax_Syntax.NT uu____54100  in
                                    [uu____54099]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___1120_54165 = b1  in
                                         let uu____54176 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___1120_54165.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___1120_54165.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____54176
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____54304  ->
                                       let new_goal =
                                         let uu____54424 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____54543 =
                                           let uu____54552 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____54552
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____54424 uu____54543
                                          in
                                       let uu____54561 = add_goals [new_goal]
                                          in
                                       bind uu____54561
                                         (fun uu____54687  ->
                                            let uu____54688 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv1.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____54688
                                              goal.FStar_Tactics_Types.opts
                                              goal.FStar_Tactics_Types.label))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____53270
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____54734 =
        let uu____54740 = cur_goal ()  in
        bind uu____54740
          (fun goal  ->
             let uu____54929 = b  in
             match uu____54929 with
             | (bv,uu____54936) ->
                 let uu____54951 =
                   let uu____55026 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____55026  in
                 (match uu____54951 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                      let steps =
                        let uu____55423 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____55423
                         in
                      let sort' =
                        normalize steps e0 bv1.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___1141_55446 = bv1  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___1141_55446.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___1141_55446.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____55571 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____55571))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____54734
  
let (revert : unit -> unit tac) =
  fun uu____55711  ->
    let uu____55717 = cur_goal ()  in
    bind uu____55717
      (fun goal  ->
         let uu____55903 =
           let uu____55969 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____55969  in
         match uu____55903 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____56341 =
                 let uu____56352 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____56352  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____56341
                in
             let uu____56390 = new_uvar "revert" env' typ'  in
             bind uu____56390
               (fun uu____56433  ->
                  match uu____56433 with
                  | (r,u_r) ->
                      let uu____56481 =
                        let uu____56487 =
                          let uu____56496 =
                            let uu____56497 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____56497.FStar_Syntax_Syntax.pos  in
                          let uu____56508 =
                            let uu____56513 =
                              let uu____56514 =
                                let uu____56527 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____56527  in
                              [uu____56514]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____56513  in
                          uu____56508 FStar_Pervasives_Native.None
                            uu____56496
                           in
                        set_solution goal uu____56487  in
                      bind uu____56481
                        (fun uu____56562  ->
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
      let uu____56712 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____56712
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____56759 = cur_goal ()  in
    bind uu____56759
      (fun goal  ->
         mlog
           (fun uu____56947  ->
              let uu____56948 = FStar_Syntax_Print.binder_to_string b  in
              let uu____56950 =
                let uu____56952 =
                  let uu____56954 =
                    let uu____56968 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____56968  in
                  FStar_All.pipe_right uu____56954 FStar_List.length  in
                FStar_All.pipe_right uu____56952 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____56948 uu____56950)
           (fun uu____57107  ->
              let uu____57108 =
                let uu____57183 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____57183  in
              match uu____57108 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bv1,bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____57631 =
                          free_in bv1 bv'.FStar_Syntax_Syntax.sort  in
                        if uu____57631
                        then
                          let uu____57639 =
                            let uu____57641 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____57641
                             in
                          fail uu____57639
                        else check1 bvs2
                     in
                  let uu____57646 =
                    let uu____57648 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv1 uu____57648  in
                  if uu____57646
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____57666 = check1 bvs  in
                     bind uu____57666
                       (fun uu____57675  ->
                          let env' = push_bvs e' bvs  in
                          let uu____57785 =
                            let uu____57807 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____57807  in
                          bind uu____57785
                            (fun uu____57837  ->
                               match uu____57837 with
                               | (ut,uvar_ut) ->
                                   let uu____57885 = set_solution goal ut  in
                                   bind uu____57885
                                     (fun uu____57893  ->
                                        let uu____57894 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                            goal.FStar_Tactics_Types.label
                                           in
                                        replace_cur uu____57894))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____58023  ->
    let uu____58029 = cur_goal ()  in
    bind uu____58029
      (fun goal  ->
         let uu____58215 =
           let uu____58281 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____58281  in
         match uu____58215 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____58460) ->
             let uu____58642 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____58642)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____58661 = cur_goal ()  in
    bind uu____58661
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____59067 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____59067  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____59188  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____59325 = cur_goal ()  in
    bind uu____59325
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____59731 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____59731  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____59852  -> add_goals [g']))
  
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
            let uu____60268 = FStar_Syntax_Subst.compress t  in
            uu____60268.FStar_Syntax_Syntax.n  in
          let uu____60279 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___1325_60300 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___1325_60300.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___1325_60300.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____60279
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____60355 =
                   let uu____60356 = FStar_Syntax_Subst.compress t1  in
                   uu____60356.FStar_Syntax_Syntax.n  in
                 match uu____60355 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____60414 = ff hd1  in
                     bind uu____60414
                       (fun hd2  ->
                          let fa uu____60466 =
                            match uu____60466 with
                            | (a,q) ->
                                let uu____60506 = ff a  in
                                bind uu____60506 (fun a1  -> ret (a1, q))
                             in
                          let uu____60552 = mapM fa args  in
                          bind uu____60552
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____60697 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____60697 with
                      | (bs1,t') ->
                          let uu____60721 =
                            let uu____60731 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____60731 t'  in
                          bind uu____60721
                            (fun t''  ->
                               let uu____60851 =
                                 let uu____60852 =
                                   let uu____60887 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____60901 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____60887, uu____60901, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____60852  in
                               ret uu____60851))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____61048 = ff hd1  in
                     bind uu____61048
                       (fun hd2  ->
                          let ffb br =
                            let uu____61081 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____61081 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____61154 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____61154  in
                                let uu____61263 = ff1 e  in
                                bind uu____61263
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____61304 = mapM ffb brs  in
                          bind uu____61304
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____61377;
                          FStar_Syntax_Syntax.lbtyp = uu____61378;
                          FStar_Syntax_Syntax.lbeff = uu____61379;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____61381;
                          FStar_Syntax_Syntax.lbpos = uu____61382;_}::[]),e)
                     ->
                     let lb =
                       let uu____61491 =
                         let uu____61492 = FStar_Syntax_Subst.compress t1  in
                         uu____61492.FStar_Syntax_Syntax.n  in
                       match uu____61491 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____61511) -> lb
                       | uu____61570 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____61611 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____61611
                         (fun def1  ->
                            ret
                              (let uu___1278_61646 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1278_61646.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1278_61646.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1278_61646.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1278_61646.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1278_61646.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1278_61646.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____61661 = fflb lb  in
                     bind uu____61661
                       (fun lb1  ->
                          let uu____61695 =
                            let uu____61704 =
                              let uu____61705 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____61705]  in
                            FStar_Syntax_Subst.open_term uu____61704 e  in
                          match uu____61695 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____61772 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____61772  in
                              let uu____61881 = ff1 e1  in
                              bind uu____61881
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____62036 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____62036
                         (fun def  ->
                            ret
                              (let uu___1296_62071 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1296_62071.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1296_62071.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1296_62071.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1296_62071.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1296_62071.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1296_62071.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____62086 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____62086 with
                      | (lbs1,e1) ->
                          let uu____62137 = mapM fflb lbs1  in
                          bind uu____62137
                            (fun lbs2  ->
                               let uu____62187 = ff e1  in
                               bind uu____62187
                                 (fun e2  ->
                                    let uu____62210 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____62210 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____62375 = ff t2  in
                     bind uu____62375
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____62449 = ff t2  in
                     bind uu____62449
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____62475 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___1320_62494 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___1320_62494.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___1320_62494.FStar_Syntax_Syntax.vars)
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
              let uu____62827 =
                FStar_TypeChecker_TcTerm.tc_term
                  (let uu___1333_62852 = env  in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___1333_62852.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___1333_62852.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___1333_62852.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___1333_62852.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_sig =
                       (uu___1333_62852.FStar_TypeChecker_Env.gamma_sig);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___1333_62852.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___1333_62852.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___1333_62852.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___1333_62852.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.attrtab =
                       (uu___1333_62852.FStar_TypeChecker_Env.attrtab);
                     FStar_TypeChecker_Env.is_pattern =
                       (uu___1333_62852.FStar_TypeChecker_Env.is_pattern);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___1333_62852.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___1333_62852.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___1333_62852.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___1333_62852.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___1333_62852.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___1333_62852.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___1333_62852.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___1333_62852.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___1333_62852.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax = true;
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___1333_62852.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.phase1 =
                       (uu___1333_62852.FStar_TypeChecker_Env.phase1);
                     FStar_TypeChecker_Env.failhard =
                       (uu___1333_62852.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___1333_62852.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.uvar_subtyping =
                       (uu___1333_62852.FStar_TypeChecker_Env.uvar_subtyping);
                     FStar_TypeChecker_Env.tc_term =
                       (uu___1333_62852.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.type_of =
                       (uu___1333_62852.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___1333_62852.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.check_type_of =
                       (uu___1333_62852.FStar_TypeChecker_Env.check_type_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___1333_62852.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (uu___1333_62852.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (uu___1333_62852.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.fv_delta_depths =
                       (uu___1333_62852.FStar_TypeChecker_Env.fv_delta_depths);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___1333_62852.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (uu___1333_62852.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.splice =
                       (uu___1333_62852.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.postprocess =
                       (uu___1333_62852.FStar_TypeChecker_Env.postprocess);
                     FStar_TypeChecker_Env.is_native_tactic =
                       (uu___1333_62852.FStar_TypeChecker_Env.is_native_tactic);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___1333_62852.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (uu___1333_62852.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (uu___1333_62852.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.nbe =
                       (uu___1333_62852.FStar_TypeChecker_Env.nbe)
                   }) t
                 in
              match uu____62827 with
              | (t1,lcomp,g) ->
                  let uu____63006 =
                    (let uu____63010 =
                       FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                     Prims.op_Negation uu____63010) ||
                      (let uu____63013 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____63013)
                     in
                  if uu____63006
                  then ret t1
                  else
                    (let rewrite_eq =
                       let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                       let uu____63050 = new_uvar "pointwise_rec" env typ  in
                       bind uu____63050
                         (fun uu____63098  ->
                            match uu____63098 with
                            | (ut,uvar_ut) ->
                                (log ps
                                   (fun uu____63154  ->
                                      let uu____63155 =
                                        FStar_Syntax_Print.term_to_string t1
                                         in
                                      let uu____63157 =
                                        FStar_Syntax_Print.term_to_string ut
                                         in
                                      FStar_Util.print2
                                        "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                        uu____63155 uu____63157);
                                 (let uu____63160 =
                                    let uu____63166 =
                                      let uu____63175 =
                                        FStar_TypeChecker_TcTerm.universe_of
                                          env typ
                                         in
                                      FStar_Syntax_Util.mk_eq2 uu____63175
                                        typ t1 ut
                                       in
                                    add_irrelevant_goal
                                      "pointwise_rec equation" env
                                      uu____63166 opts label1
                                     in
                                  bind uu____63160
                                    (fun uu____63183  ->
                                       let uu____63184 =
                                         bind tau
                                           (fun uu____63201  ->
                                              let ut1 =
                                                FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                  env ut
                                                 in
                                              log ps
                                                (fun uu____63215  ->
                                                   let uu____63216 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1
                                                      in
                                                   let uu____63218 =
                                                     FStar_Syntax_Print.term_to_string
                                                       ut1
                                                      in
                                                   FStar_Util.print2
                                                     "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                     uu____63216 uu____63218);
                                              ret ut1)
                                          in
                                       focus uu____63184))))
                        in
                     let uu____63229 = catch rewrite_eq  in
                     bind uu____63229
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
          let uu____63930 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____63930
            (fun t1  ->
               let uu____63950 =
                 f env
                   (let uu___1410_63965 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___1410_63965.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___1410_63965.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____63950
                 (fun uu____63997  ->
                    match uu____63997 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____64043 =
                               let uu____64044 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____64044.FStar_Syntax_Syntax.n  in
                             match uu____64043 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____64112 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____64112
                                   (fun uu____64149  ->
                                      match uu____64149 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____64184 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____64184
                                            (fun uu____64215  ->
                                               match uu____64215 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___1390_64260 =
                                                         t3  in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___1390_64260.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___1390_64260.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____64350 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____64350 with
                                  | (bs1,t') ->
                                      let uu____64384 =
                                        let uu____64398 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____64398 ctrl1 t'
                                         in
                                      bind uu____64384
                                        (fun uu____64529  ->
                                           match uu____64529 with
                                           | (t'',ctrl2) ->
                                               let uu____64563 =
                                                 let uu____64574 =
                                                   let uu___1403_64585 = t4
                                                      in
                                                   let uu____64596 =
                                                     let uu____64597 =
                                                       let uu____64632 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____64646 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____64632,
                                                         uu____64646, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____64597
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____64596;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___1403_64585.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___1403_64585.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____64574, ctrl2)  in
                                               ret uu____64563))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____64757 -> ret (t3, ctrl1))))

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
              let uu____64935 = ctrl_tac_fold f env ctrl t  in
              bind uu____64935
                (fun uu____64967  ->
                   match uu____64967 with
                   | (t1,ctrl1) ->
                       let uu____64997 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____64997
                         (fun uu____65024  ->
                            match uu____65024 with
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
                let uu____65399 =
                  let uu____65410 =
                    add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                      opts label1
                     in
                  bind uu____65410
                    (fun uu____65424  ->
                       let uu____65425 = ctrl t1  in
                       bind uu____65425
                         (fun res  ->
                            let uu____65454 = trivial ()  in
                            bind uu____65454 (fun uu____65466  -> ret res)))
                   in
                bind uu____65399
                  (fun uu____65488  ->
                     match uu____65488 with
                     | (should_rewrite,ctrl1) ->
                         if Prims.op_Negation should_rewrite
                         then ret (t1, ctrl1)
                         else
                           (let uu____65539 =
                              FStar_TypeChecker_TcTerm.tc_term
                                (let uu___1440_65564 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___1440_65564.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___1440_65564.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___1440_65564.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___1440_65564.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___1440_65564.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___1440_65564.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___1440_65564.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___1440_65564.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___1440_65564.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___1440_65564.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___1440_65564.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___1440_65564.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___1440_65564.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___1440_65564.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___1440_65564.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___1440_65564.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___1440_65564.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___1440_65564.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___1440_65564.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___1440_65564.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___1440_65564.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___1440_65564.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___1440_65564.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___1440_65564.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___1440_65564.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___1440_65564.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___1440_65564.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___1440_65564.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___1440_65564.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___1440_65564.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___1440_65564.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___1440_65564.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___1440_65564.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___1440_65564.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___1440_65564.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___1440_65564.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___1440_65564.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___1440_65564.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___1440_65564.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___1440_65564.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___1440_65564.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___1440_65564.FStar_TypeChecker_Env.nbe)
                                 }) t1
                               in
                            match uu____65539 with
                            | (t2,lcomp,g) ->
                                let uu____65722 =
                                  (let uu____65726 =
                                     FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                       lcomp
                                      in
                                   Prims.op_Negation uu____65726) ||
                                    (let uu____65729 =
                                       FStar_TypeChecker_Env.is_trivial g  in
                                     Prims.op_Negation uu____65729)
                                   in
                                if uu____65722
                                then ret (t2, globalStop)
                                else
                                  (let typ =
                                     lcomp.FStar_Syntax_Syntax.res_typ  in
                                   let uu____65768 =
                                     new_uvar "pointwise_rec" env typ  in
                                   bind uu____65768
                                     (fun uu____65820  ->
                                        match uu____65820 with
                                        | (ut,uvar_ut) ->
                                            (log ps
                                               (fun uu____65880  ->
                                                  let uu____65881 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t2
                                                     in
                                                  let uu____65883 =
                                                    FStar_Syntax_Print.term_to_string
                                                      ut
                                                     in
                                                  FStar_Util.print2
                                                    "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                    uu____65881 uu____65883);
                                             (let uu____65886 =
                                                let uu____65892 =
                                                  let uu____65901 =
                                                    FStar_TypeChecker_TcTerm.universe_of
                                                      env typ
                                                     in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____65901 typ t2 ut
                                                   in
                                                add_irrelevant_goal
                                                  "rewrite_rec equation" env
                                                  uu____65892 opts label1
                                                 in
                                              bind uu____65886
                                                (fun uu____65913  ->
                                                   let uu____65914 =
                                                     bind rewriter
                                                       (fun uu____65939  ->
                                                          let ut1 =
                                                            FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                              env ut
                                                             in
                                                          log ps
                                                            (fun uu____65953 
                                                               ->
                                                               let uu____65954
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   t2
                                                                  in
                                                               let uu____65956
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   ut1
                                                                  in
                                                               FStar_Util.print2
                                                                 "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                                 uu____65954
                                                                 uu____65956);
                                                          ret (ut1, ctrl1))
                                                      in
                                                   focus uu____65914)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term -> (Prims.bool * FStar_BigInt.t) tac) ->
    unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____66033 =
        bind get
          (fun ps  ->
             let uu____66180 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____66180 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____67173  ->
                       let uu____67174 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____67174);
                  bind dismiss_all
                    (fun uu____67179  ->
                       let uu____67180 =
                         let uu____67194 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____67194
                           keepGoing gt1
                          in
                       bind uu____67180
                         (fun uu____67316  ->
                            match uu____67316 with
                            | (gt',uu____67331) ->
                                (log ps
                                   (fun uu____67343  ->
                                      let uu____67344 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____67344);
                                 (let uu____67347 = push_goals gs  in
                                  bind uu____67347
                                    (fun uu____67355  ->
                                       let uu____67356 =
                                         let uu____67418 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____67418]  in
                                       add_goals uu____67356)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____66033
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____67694 =
        bind get
          (fun ps  ->
             let uu____67841 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____67841 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____68834  ->
                       let uu____68835 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____68835);
                  bind dismiss_all
                    (fun uu____68840  ->
                       let uu____68841 =
                         let uu____68851 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____68851 gt1
                          in
                       bind uu____68841
                         (fun gt'  ->
                            log ps
                              (fun uu____68975  ->
                                 let uu____68976 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____68976);
                            (let uu____68979 = push_goals gs  in
                             bind uu____68979
                               (fun uu____68987  ->
                                  let uu____68988 =
                                    let uu____69050 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____69050]  in
                                  add_goals uu____68988))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____67694
  
let (trefl : unit -> unit tac) =
  fun uu____69308  ->
    let uu____69314 =
      let uu____69320 = cur_goal ()  in
      bind uu____69320
        (fun g  ->
           let uu____69518 =
             let uu____69527 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____69527  in
           match uu____69518 with
           | FStar_Pervasives_Native.Some t ->
               let uu____69554 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____69554 with
                | (hd1,args) ->
                    let uu____69620 =
                      let uu____69637 =
                        let uu____69638 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____69638.FStar_Syntax_Syntax.n  in
                      (uu____69637, args)  in
                    (match uu____69620 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____69667::(l,uu____69669)::(r,uu____69671)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____69761 =
                           let uu____69768 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____69768 l r  in
                         bind uu____69761
                           (fun b  ->
                              if b
                              then solve' g FStar_Syntax_Util.exp_unit
                              else
                                (let l1 =
                                   let uu____69898 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____69898 l
                                    in
                                 let r1 =
                                   let uu____70016 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____70016 r
                                    in
                                 let uu____70125 =
                                   let uu____70132 =
                                     FStar_Tactics_Types.goal_env g  in
                                   do_unify uu____70132 l1 r1  in
                                 bind uu____70125
                                   (fun b1  ->
                                      if b1
                                      then
                                        solve' g FStar_Syntax_Util.exp_unit
                                      else
                                        (let uu____70253 =
                                           let uu____70255 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____70255 l1  in
                                         let uu____70364 =
                                           let uu____70366 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____70366 r1  in
                                         fail2
                                           "not a trivial equality ((%s) vs (%s))"
                                           uu____70253 uu____70364))))
                     | (hd2,uu____70477) ->
                         let uu____70502 =
                           let uu____70504 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____70504 t  in
                         fail1 "trefl: not an equality (%s)" uu____70502))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____69314
  
let (dup : unit -> unit tac) =
  fun uu____70642  ->
    let uu____70648 = cur_goal ()  in
    bind uu____70648
      (fun g  ->
         let uu____70834 =
           let uu____70856 = FStar_Tactics_Types.goal_env g  in
           let uu____70965 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____70856 uu____70965  in
         bind uu____70834
           (fun uu____70995  ->
              match uu____70995 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___1532_71162 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___1532_71162.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___1532_71162.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___1532_71162.FStar_Tactics_Types.is_guard);
                      FStar_Tactics_Types.label =
                        (uu___1532_71162.FStar_Tactics_Types.label)
                    }  in
                  bind __dismiss
                    (fun uu____71283  ->
                       let uu____71284 =
                         let uu____71290 = FStar_Tactics_Types.goal_env g  in
                         let uu____71399 =
                           let uu____71408 =
                             let uu____71409 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____71518 =
                               FStar_Tactics_Types.goal_type g  in
                             FStar_TypeChecker_TcTerm.universe_of uu____71409
                               uu____71518
                              in
                           let uu____71527 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____71536 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____71408 uu____71527 u
                             uu____71536
                            in
                         add_irrelevant_goal "dup equation" uu____71290
                           uu____71399 g.FStar_Tactics_Types.opts
                           g.FStar_Tactics_Types.label
                          in
                       bind uu____71284
                         (fun uu____71548  ->
                            let uu____71549 = add_goals [g']  in
                            bind uu____71549 (fun uu____71674  -> ret ())))))
  
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
              let uu____71800 = f x y  in
              if uu____71800 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____71823 -> (acc, l11, l21)  in
        let uu____71838 = aux [] l1 l2  in
        match uu____71838 with | (pr,t1,t2) -> ((FStar_List.rev pr), t1, t2)
  
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
      let uu____72349 = get_phi g1  in
      match uu____72349 with
      | FStar_Pervasives_Native.None  -> fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____72493 = get_phi g2  in
          (match uu____72493 with
           | FStar_Pervasives_Native.None  -> fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let uu____72643 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2)
                  in
               (match uu____72643 with
                | (gamma,r1,r2) ->
                    let t1 =
                      let uu____72744 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1)
                         in
                      close_forall_no_univs1 uu____72744 phi1  in
                    let t2 =
                      let uu____72767 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2)
                         in
                      close_forall_no_univs1 uu____72767 phi2  in
                    let uu____72781 =
                      set_solution g1 FStar_Syntax_Util.exp_unit  in
                    bind uu____72781
                      (fun uu____72848  ->
                         let uu____72849 =
                           set_solution g2 FStar_Syntax_Util.exp_unit  in
                         bind uu____72849
                           (fun uu____72918  ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2  in
                              let nenv =
                                let uu___1583_73039 =
                                  FStar_Tactics_Types.goal_env g1  in
                                let uu____73148 =
                                  FStar_Util.smap_create
                                    (Prims.parse_int "100")
                                   in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___1583_73039.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___1583_73039.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___1583_73039.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___1583_73039.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____73148;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___1583_73039.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___1583_73039.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___1583_73039.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___1583_73039.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___1583_73039.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___1583_73039.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___1583_73039.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___1583_73039.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___1583_73039.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___1583_73039.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___1583_73039.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___1583_73039.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___1583_73039.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___1583_73039.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___1583_73039.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___1583_73039.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___1583_73039.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___1583_73039.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___1583_73039.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___1583_73039.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___1583_73039.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___1583_73039.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___1583_73039.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___1583_73039.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___1583_73039.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___1583_73039.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___1583_73039.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___1583_73039.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___1583_73039.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___1583_73039.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___1583_73039.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___1583_73039.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___1583_73039.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___1583_73039.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___1583_73039.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___1583_73039.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___1583_73039.FStar_TypeChecker_Env.nbe)
                                }  in
                              let uu____73152 =
                                mk_irrelevant_goal "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                  g1.FStar_Tactics_Types.label
                                 in
                              bind uu____73152
                                (fun goal  ->
                                   mlog
                                     (fun uu____73460  ->
                                        let uu____73461 =
                                          goal_to_string_verbose g1  in
                                        let uu____73463 =
                                          goal_to_string_verbose g2  in
                                        let uu____73465 =
                                          goal_to_string_verbose goal  in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____73461 uu____73463 uu____73465)
                                     (fun uu____73469  -> ret goal))))))
  
let (join : unit -> unit tac) =
  fun uu____73539  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____73990 =
               set
                 (let uu___1598_73998 = ps  in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___1598_73998.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.main_goal =
                      (uu___1598_73998.FStar_Tactics_Types.main_goal);
                    FStar_Tactics_Types.all_implicits =
                      (uu___1598_73998.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___1598_73998.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___1598_73998.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___1598_73998.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___1598_73998.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___1598_73998.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___1598_73998.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___1598_73998.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___1598_73998.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___1598_73998.FStar_Tactics_Types.local_state)
                  })
                in
             bind uu____73990
               (fun uu____74135  ->
                  let uu____74136 = join_goals g1 g2  in
                  bind uu____74136 (fun g12  -> add_goals [g12]))
         | uu____74439 -> fail "join: less than 2 goals")
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____74520 =
      let uu____74526 = cur_goal ()  in
      bind uu____74526
        (fun g  ->
           FStar_Options.push ();
           (let uu____74719 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____74719);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___1609_74847 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1609_74847.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___1609_74847.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___1609_74847.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1609_74847.FStar_Tactics_Types.label)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____74520
  
let (top_env : unit -> env tac) =
  fun uu____75045  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____75473  ->
    let uu____75480 = cur_goal ()  in
    bind uu____75480
      (fun g  ->
         let uu____75667 =
           (FStar_Options.lax ()) ||
             (let uu____75670 = FStar_Tactics_Types.goal_env g  in
              uu____75670.FStar_TypeChecker_Env.lax)
            in
         ret uu____75667)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____75825 =
        mlog
          (fun uu____75841  ->
             let uu____75842 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____75842)
          (fun uu____75847  ->
             let uu____75848 = cur_goal ()  in
             bind uu____75848
               (fun goal  ->
                  let env =
                    let uu____76148 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____76148 ty  in
                  let uu____76257 = __tc_ghost env tm  in
                  bind uu____76257
                    (fun uu____76307  ->
                       match uu____76307 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____76368  ->
                                let uu____76369 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____76369)
                             (fun uu____76373  ->
                                mlog
                                  (fun uu____76380  ->
                                     let uu____76381 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____76381)
                                  (fun uu____76386  ->
                                     let uu____76387 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____76387
                                       (fun uu____76399  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____75825
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____76576 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____76612 =
              let uu____76634 =
                let uu____76643 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____76643
                 in
              new_uvar "uvar_env.2" env uu____76634  in
            bind uu____76612
              (fun uu____76692  ->
                 match uu____76692 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____76576
        (fun typ  ->
           let uu____76763 = new_uvar "uvar_env" env typ  in
           bind uu____76763
             (fun uu____76809  ->
                match uu____76809 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____76889 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____77153 -> g.FStar_Tactics_Types.opts
             | uu____77333 -> FStar_Options.peek ()  in
           let uu____77395 = FStar_Syntax_Util.head_and_args t  in
           match uu____77395 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____77426);
                FStar_Syntax_Syntax.pos = uu____77427;
                FStar_Syntax_Syntax.vars = uu____77428;_},uu____77429)
               ->
               let env1 =
                 let uu___1663_77611 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___1663_77611.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___1663_77611.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___1663_77611.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___1663_77611.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___1663_77611.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___1663_77611.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___1663_77611.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___1663_77611.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___1663_77611.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___1663_77611.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___1663_77611.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___1663_77611.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___1663_77611.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___1663_77611.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___1663_77611.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___1663_77611.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___1663_77611.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___1663_77611.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___1663_77611.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___1663_77611.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___1663_77611.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___1663_77611.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___1663_77611.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___1663_77611.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___1663_77611.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___1663_77611.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___1663_77611.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___1663_77611.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___1663_77611.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___1663_77611.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___1663_77611.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___1663_77611.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___1663_77611.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___1663_77611.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___1663_77611.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___1663_77611.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___1663_77611.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___1663_77611.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___1663_77611.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___1663_77611.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___1663_77611.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___1663_77611.FStar_TypeChecker_Env.nbe)
                 }  in
               let g =
                 FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false ""  in
               let uu____77841 =
                 let uu____77903 = bnorm_goal g  in [uu____77903]  in
               add_goals uu____77841
           | uu____78140 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____76889
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____78231 = if b then t2 else ret false  in
             bind uu____78231 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____78266 = trytac comp  in
      bind uu____78266
        (fun uu___4_78281  ->
           match uu___4_78281 with
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
        let uu____78459 =
          bind get
            (fun ps  ->
               let uu____78604 = __tc e t1  in
               bind uu____78604
                 (fun uu____78652  ->
                    match uu____78652 with
                    | (t11,ty1,g1) ->
                        let uu____78704 = __tc e t2  in
                        bind uu____78704
                          (fun uu____78752  ->
                             match uu____78752 with
                             | (t21,ty2,g2) ->
                                 let uu____78804 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____78804
                                   (fun uu____78814  ->
                                      let uu____78815 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____78815
                                        (fun uu____78826  ->
                                           let uu____78827 =
                                             do_unify e ty1 ty2  in
                                           let uu____78834 =
                                             do_unify e t11 t21  in
                                           tac_and uu____78827 uu____78834)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____78459
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____78897  ->
             let uu____78898 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____78898
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
        (fun uu____78964  ->
           let uu____78965 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____78965)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____79005 =
      mlog
        (fun uu____79013  ->
           let uu____79014 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____79014)
        (fun uu____79019  ->
           let uu____79020 = cur_goal ()  in
           bind uu____79020
             (fun g  ->
                let uu____79206 =
                  let uu____79230 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____79230 ty  in
                bind uu____79206
                  (fun uu____79362  ->
                     match uu____79362 with
                     | (ty1,uu____79387,guard) ->
                         let uu____79413 =
                           let uu____79419 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____79419 guard  in
                         bind uu____79413
                           (fun uu____79531  ->
                              let uu____79532 =
                                let uu____79539 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____79648 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____79539 uu____79648 ty1  in
                              bind uu____79532
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____79668 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____79668
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops]  in
                                      let ng =
                                        let uu____79801 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____79910 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____79801
                                          uu____79910
                                         in
                                      let nty =
                                        let uu____79928 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____79928 ty1  in
                                      let uu____80037 =
                                        let uu____80044 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____80044 ng nty  in
                                      bind uu____80037
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____80164 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____80164
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____79005
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) Prims.list tac)
  =
  fun s_tm  ->
    let uu____80388 =
      let uu____80403 = cur_goal ()  in
      bind uu____80403
        (fun g  ->
           let uu____80598 =
             let uu____80622 = FStar_Tactics_Types.goal_env g  in
             __tc uu____80622 s_tm  in
           bind uu____80598
             (fun uu____80763  ->
                match uu____80763 with
                | (s_tm1,s_ty,guard) ->
                    let uu____80823 =
                      let uu____80829 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____80829 guard  in
                    bind uu____80823
                      (fun uu____80953  ->
                         let uu____80954 =
                           FStar_Syntax_Util.head_and_args' s_ty  in
                         match uu____80954 with
                         | (h,args) ->
                             let uu____81029 =
                               let uu____81042 =
                                 let uu____81043 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____81043.FStar_Syntax_Syntax.n  in
                               match uu____81042 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____81081;
                                      FStar_Syntax_Syntax.vars = uu____81082;_},us)
                                   -> ret (fv, us)
                               | uu____81109 -> fail "type is not an fv"  in
                             bind uu____81029
                               (fun uu____81139  ->
                                  match uu____81139 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____81178 =
                                        let uu____81186 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____81186 t_lid
                                         in
                                      (match uu____81178 with
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
                                                  (fun uu____81412  ->
                                                     let uu____81413 =
                                                       FStar_Syntax_Subst.open_term
                                                         t_ps t_ty
                                                        in
                                                     match uu____81413 with
                                                     | (t_ps1,t_ty1) ->
                                                         let uu____81446 =
                                                           mapM
                                                             (fun c_lid  ->
                                                                let uu____81609
                                                                  =
                                                                  let uu____81617
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                  FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____81617
                                                                    c_lid
                                                                   in
                                                                match uu____81609
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
                                                                    uu____82108
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
                                                                    let uu____82121
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____82121
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____82227
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____82227
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____82362
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs
                                                                     in
                                                                    (match uu____82362
                                                                    with
                                                                    | 
                                                                    (d_ps,bs1)
                                                                    ->
                                                                    let uu____82535
                                                                    =
                                                                    let uu____82537
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp  in
                                                                    Prims.op_Negation
                                                                    uu____82537
                                                                     in
                                                                    failwhen
                                                                    uu____82535
                                                                    "not total?"
                                                                    (fun
                                                                    uu____82618
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
                                                                    uu___5_82641
                                                                    =
                                                                    match uu___5_82641
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____82645)
                                                                    -> true
                                                                    | 
                                                                    uu____82648
                                                                    -> false
                                                                     in
                                                                    let uu____82652
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____82652
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
                                                                    uu____82950
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
                                                                    uu____83039
                                                                     ->
                                                                    match uu____83039
                                                                    with
                                                                    | 
                                                                    ((bv,uu____83068),
                                                                    (t,uu____83070))
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
                                                                    uu____83191
                                                                     ->
                                                                    match uu____83191
                                                                    with
                                                                    | 
                                                                    ((bv,uu____83230),
                                                                    (t,uu____83232))
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
                                                                    uu____83341
                                                                     ->
                                                                    match uu____83341
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
                                                                    let uu____83548
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___1827_83636
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___1827_83636.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1827_83636.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1827_83636.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___1827_83636.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___1827_83636.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1827_83636.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1827_83636.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1827_83636.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1827_83636.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___1827_83636.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___1827_83636.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___1827_83636.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1827_83636.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1827_83636.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1827_83636.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1827_83636.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1827_83636.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1827_83636.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1827_83636.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___1827_83636.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___1827_83636.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1827_83636.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1827_83636.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1827_83636.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1827_83636.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1827_83636.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1827_83636.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1827_83636.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1827_83636.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1827_83636.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1827_83636.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1827_83636.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1827_83636.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1827_83636.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___1827_83636.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1827_83636.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1827_83636.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___1827_83636.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1827_83636.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1827_83636.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1827_83636.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1827_83636.FStar_TypeChecker_Env.nbe)
                                                                    }) s_ty
                                                                    pat  in
                                                                    match uu____83548
                                                                    with
                                                                    | 
                                                                    (uu____83823,uu____83824,uu____83825,pat_t,uu____83827,_guard_pat)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____83986
                                                                    =
                                                                    let uu____83995
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____83995
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____83986
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____84016
                                                                    =
                                                                    let uu____84030
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____84030]
                                                                     in
                                                                    let uu____84064
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____84016
                                                                    uu____84064
                                                                     in
                                                                    let nty =
                                                                    let uu____84086
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____84086
                                                                     in
                                                                    let uu____84097
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____84097
                                                                    (fun
                                                                    uu____84216
                                                                     ->
                                                                    match uu____84216
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
                                                                    let uu____84478
                                                                    =
                                                                    let uu____84493
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____84493]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____84478
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____84556
                                                                    =
                                                                    let uu____84629
                                                                    =
                                                                    let uu____84637
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2)  in
                                                                    (fv1,
                                                                    uu____84637)
                                                                     in
                                                                    (g', br,
                                                                    uu____84629)
                                                                     in
                                                                    ret
                                                                    uu____84556))))))
                                                                    | 
                                                                    uu____84790
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                             c_lids
                                                            in
                                                         bind uu____81446
                                                           (fun goal_brs  ->
                                                              let uu____85029
                                                                =
                                                                FStar_List.unzip3
                                                                  goal_brs
                                                                 in
                                                              match uu____85029
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
                                                                  let uu____85379
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                  bind
                                                                    uu____85379
                                                                    (
                                                                    fun
                                                                    uu____85396
                                                                     ->
                                                                    let uu____85397
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____85397
                                                                    (fun
                                                                    uu____85413
                                                                     ->
                                                                    ret infos))))
                                            | uu____85423 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____80388
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____85490::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____85520 = init xs  in x :: uu____85520
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____85547 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      let t3 = FStar_Syntax_Util.unlazy_emb t2  in
      match t3.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____85586) -> inspect t4
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____85717 = last args  in
          (match uu____85717 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____85766 =
                 let uu____85767 =
                   let uu____85776 =
                     let uu____85785 =
                       let uu____85790 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____85790  in
                     uu____85785 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____85776, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____85767  in
               FStar_All.pipe_left ret uu____85766)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____85816,uu____85817) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
          let uu____85937 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____85937 with
           | (bs1,t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____86020 =
                      let uu____86021 =
                        let uu____86030 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____86030)  in
                      FStar_Reflection_Data.Tv_Abs uu____86021  in
                    FStar_All.pipe_left ret uu____86020))
      | FStar_Syntax_Syntax.Tm_type uu____86048 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____86097 ->
          let uu____86121 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____86121 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____86203 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____86203 with
           | (b',t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____86306 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____86341 =
            let uu____86342 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____86342  in
          FStar_All.pipe_left ret uu____86341
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____86382 =
            let uu____86383 =
              let uu____86388 =
                let uu____86389 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____86389  in
              (uu____86388, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____86383  in
          FStar_All.pipe_left ret uu____86382
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____86496 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____86528 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____86528 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____86631 ->
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
             | FStar_Util.Inr uu____86755 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____86786 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____86786 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____86883 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____86929 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____87027 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____87027
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____87060 =
                  let uu____87070 =
                    FStar_List.map
                      (fun uu____87086  ->
                         match uu____87086 with
                         | (p1,uu____87095) -> inspect_pat p1) ps
                     in
                  (fv, uu____87070)  in
                FStar_Reflection_Data.Pat_Cons uu____87060
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
              (fun uu___6_87289  ->
                 match uu___6_87289 with
                 | (pat,uu____87323,t5) ->
                     let uu____87363 = inspect_pat pat  in (uu____87363, t5))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____87386 ->
          ((let uu____87388 =
              let uu____87394 =
                let uu____87396 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____87398 = FStar_Syntax_Print.term_to_string t3  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____87396 uu____87398
                 in
              (FStar_Errors.Warning_CantInspect, uu____87394)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____87388);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____85547
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____87438 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____87438
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____87470 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____87470
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____87500 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____87500
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____87546 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____87546
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____87614 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____87614
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____87679 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____87679
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____87764 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____87764
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____87791 =
          let uu____87800 =
            let uu____87807 =
              let uu____87808 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____87808  in
            FStar_Syntax_Syntax.mk uu____87807  in
          uu____87800 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____87791
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____87828 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____87828
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____87916 =
          let uu____87925 =
            let uu____87932 =
              let uu____87933 =
                let uu____87958 =
                  let uu____87969 =
                    let uu____87970 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____87970]  in
                  FStar_Syntax_Subst.close uu____87969 t2  in
                ((false, [lb]), uu____87958)  in
              FStar_Syntax_Syntax.Tm_let uu____87933  in
            FStar_Syntax_Syntax.mk uu____87932  in
          uu____87925 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____87916
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____88128 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____88128 with
         | (lbs,body) ->
             let uu____88197 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____88197)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____88289 =
                let uu____88290 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____88290  in
              FStar_All.pipe_left wrap uu____88289
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____88303 =
                let uu____88304 =
                  let uu____88324 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____88345 = pack_pat p1  in
                         (uu____88345, false)) ps
                     in
                  (fv, uu____88324)  in
                FStar_Syntax_Syntax.Pat_cons uu____88304  in
              FStar_All.pipe_left wrap uu____88303
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
            (fun uu___7_88457  ->
               match uu___7_88457 with
               | (pat,t1) ->
                   let uu____88494 = pack_pat pat  in
                   (uu____88494, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____88584 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____88584
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____88674 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____88674
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____88811 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____88811
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____88917 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____88917
  
let (lget :
  FStar_Reflection_Data.typ -> Prims.string -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun k  ->
      let uu____88982 =
        bind get
          (fun ps  ->
             let uu____89133 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____89133 with
             | FStar_Pervasives_Native.None  -> fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
      FStar_All.pipe_left (wrap_err "lget") uu____88982
  
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit tac)
  =
  fun _ty  ->
    fun k  ->
      fun t  ->
        let uu____89238 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___2125_89516 = ps  in
                 let uu____89651 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t
                    in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___2125_89516.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___2125_89516.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___2125_89516.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___2125_89516.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___2125_89516.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___2125_89516.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___2125_89516.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___2125_89516.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___2125_89516.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___2125_89516.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___2125_89516.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___2125_89516.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____89651
                 }  in
               set ps1)
           in
        FStar_All.pipe_left (wrap_err "lset") uu____89238
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal * FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun typ  ->
      let uu____89934 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____89934 with
      | (u,ctx_uvars,g_u) ->
          let uu____90078 = FStar_List.hd ctx_uvars  in
          (match uu____90078 with
           | (ctx_uvar,uu____90171) ->
               let g =
                 let uu____90307 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____90307 false
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
        let uu____90580 = goal_of_goal_ty env typ  in
        match uu____90580 with
        | (g,g_u) ->
            let ps =
              let uu____90986 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "TacVerbose")
                 in
              let uu____90989 = FStar_Util.psmap_empty ()  in
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
                FStar_Tactics_Types.tac_verb_dbg = uu____90986;
                FStar_Tactics_Types.local_state = uu____90989
              }  in
            let uu____91251 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____91251)
  