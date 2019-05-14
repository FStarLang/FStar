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
  
let (unshadow :
  FStar_Reflection_Data.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Reflection_Data.binders * FStar_Syntax_Syntax.term))
  =
  fun bs  ->
    fun t  ->
      let s b = (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText  in
      let sset bv s1 =
        FStar_Syntax_Syntax.gen_bv s1
          (FStar_Pervasives_Native.Some
             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
          bv.FStar_Syntax_Syntax.sort
         in
      let fresh_until b f =
        let rec aux i =
          let t1 =
            let uu____3395 =
              let uu____3397 = FStar_Util.string_of_int i  in
              Prims.op_Hat "'" uu____3397  in
            Prims.op_Hat b uu____3395  in
          let uu____3400 = f t1  in
          if uu____3400 then t1 else aux (i + (Prims.parse_int "1"))  in
        let uu____3407 = f b  in
        if uu____3407 then b else aux (Prims.parse_int "0")  in
      let rec go seen subst1 bs1 bs' t1 =
        match bs1 with
        | [] ->
            let uu____3563 = FStar_Syntax_Subst.subst subst1 t1  in
            ((FStar_List.rev bs'), uu____3563)
        | b::bs2 ->
            let uu____3637 = FStar_Syntax_Subst.subst_binders subst1 [b]  in
            (match uu____3637 with
             | b1::[] ->
                 let uu____3715 = b1  in
                 (match uu____3715 with
                  | (bv0,q) ->
                      let nbs =
                        fresh_until (s bv0)
                          (fun s1  ->
                             Prims.op_Negation (FStar_List.mem s1 seen))
                         in
                      let bv = sset bv0 nbs  in
                      let b2 = (bv, q)  in
                      let uu____3800 =
                        let uu____3803 =
                          let uu____3806 =
                            let uu____3807 =
                              let uu____3823 =
                                FStar_Syntax_Syntax.bv_to_name bv  in
                              (bv0, uu____3823)  in
                            FStar_Syntax_Syntax.NT uu____3807  in
                          [uu____3806]  in
                        FStar_List.append subst1 uu____3803  in
                      go (nbs :: seen) uu____3800 bs2 (b2 :: bs') t1))
         in
      go [] [] bs [] t
  
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
            let uu____4164 = FStar_Options.print_implicits ()  in
            if uu____4164
            then
              let uu____4168 = FStar_Tactics_Types.goal_env g  in
              let uu____4277 = FStar_Tactics_Types.goal_witness g  in
              tts uu____4168 uu____4277
            else
              (let uu____4288 =
                 get_uvar_solved g.FStar_Tactics_Types.goal_ctx_uvar  in
               match uu____4288 with
               | FStar_Pervasives_Native.None  -> "_"
               | FStar_Pervasives_Native.Some t ->
                   let uu____4310 = FStar_Tactics_Types.goal_env g  in
                   let uu____4419 = FStar_Tactics_Types.goal_witness g  in
                   tts uu____4310 uu____4419)
             in
          let num =
            match maybe_num with
            | FStar_Pervasives_Native.None  -> ""
            | FStar_Pervasives_Native.Some (i,n1) ->
                let uu____4450 = FStar_Util.string_of_int i  in
                let uu____4452 = FStar_Util.string_of_int n1  in
                FStar_Util.format2 " %s/%s" uu____4450 uu____4452
             in
          let maybe_label =
            match g.FStar_Tactics_Types.label with
            | "" -> ""
            | l -> Prims.op_Hat " (" (Prims.op_Hat l ")")  in
          let goal_binders =
            (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
             in
          let goal_ty =
            (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
             in
          let uu____4489 = unshadow goal_binders goal_ty  in
          match uu____4489 with
          | (goal_binders1,goal_ty1) ->
              let actual_goal =
                if ps.FStar_Tactics_Types.tac_verb_dbg
                then goal_to_string_verbose g
                else
                  (let uu____4515 =
                     FStar_Syntax_Print.binders_to_string ", " goal_binders1
                      in
                   let uu____4518 =
                     let uu____4520 = FStar_Tactics_Types.goal_env g  in
                     tts uu____4520 goal_ty1  in
                   FStar_Util.format3 "%s |- %s : %s\n" uu____4515 w
                     uu____4518)
                 in
              FStar_Util.format4 "%s%s%s:\n%s\n" kind num maybe_label
                actual_goal
  
let (tacprint : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      let uu____4655 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____4655
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____4680 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____4680
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____4712 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____4712
  
let (get_phi :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun g  ->
    let uu____4851 =
      let uu____4860 = FStar_Tactics_Types.goal_env g  in
      let uu____4969 = FStar_Tactics_Types.goal_type g  in
      FStar_TypeChecker_Normalize.unfold_whnf uu____4860 uu____4969  in
    FStar_Syntax_Util.un_squash uu____4851
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  -> let uu____5104 = get_phi g  in FStar_Option.isSome uu____5104 
let (print : Prims.string -> unit tac) = fun msg  -> tacprint msg; ret () 
let (debugging : unit -> Prims.bool tac) =
  fun uu____5145  ->
    bind get
      (fun ps  ->
         let uu____5290 =
           FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
             (FStar_Options.Other "Tac")
            in
         ret uu____5290)
  
let (ps_to_string :
  (Prims.string * FStar_Tactics_Types.proofstate) -> Prims.string) =
  fun uu____5372  ->
    match uu____5372 with
    | (msg,ps) ->
        let p_imp imp =
          FStar_Syntax_Print.uvar_to_string
            (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
           in
        let n_active = FStar_List.length ps.FStar_Tactics_Types.goals  in
        let n_smt = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
        let n1 = n_active + n_smt  in
        let uu____5721 =
          let uu____5725 =
            let uu____5729 =
              let uu____5731 =
                FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
              FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____5731
                msg
               in
            let uu____5734 =
              let uu____5738 =
                if
                  ps.FStar_Tactics_Types.entry_range <>
                    FStar_Range.dummyRange
                then
                  let uu____5742 =
                    FStar_Range.string_of_def_range
                      ps.FStar_Tactics_Types.entry_range
                     in
                  FStar_Util.format1 "Location: %s\n" uu____5742
                else ""  in
              let uu____5748 =
                let uu____5752 =
                  let uu____5754 =
                    FStar_TypeChecker_Env.debug
                      ps.FStar_Tactics_Types.main_context
                      (FStar_Options.Other "Imp")
                     in
                  if uu____5754
                  then
                    let uu____5759 =
                      FStar_Common.string_of_list p_imp
                        ps.FStar_Tactics_Types.all_implicits
                       in
                    FStar_Util.format1 "Imps: %s\n" uu____5759
                  else ""  in
                [uu____5752]  in
              uu____5738 :: uu____5748  in
            uu____5729 :: uu____5734  in
          let uu____5773 =
            let uu____5777 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "Goal"
                       (FStar_Pervasives_Native.Some
                          (((Prims.parse_int "1") + i), n1)) ps g)
                ps.FStar_Tactics_Types.goals
               in
            let uu____5915 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "SMT Goal"
                       (FStar_Pervasives_Native.Some
                          ((((Prims.parse_int "1") + n_active) + i), n1)) ps
                       g) ps.FStar_Tactics_Types.smt_goals
               in
            FStar_List.append uu____5777 uu____5915  in
          FStar_List.append uu____5725 uu____5773  in
        FStar_String.concat "" uu____5721
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
       in
    let g_type = FStar_Tactics_Types.goal_type g  in
    let uu____6203 = unshadow g_binders g_type  in
    match uu____6203 with
    | (g_binders1,g_type1) ->
        let j_binders =
          let uu____6223 =
            let uu____6224 = FStar_Tactics_Types.goal_env g  in
            FStar_TypeChecker_Env.dsenv uu____6224  in
          FStar_Syntax_Print.binders_to_json uu____6223 g_binders1  in
        let uu____6333 =
          let uu____6341 =
            let uu____6349 =
              let uu____6355 =
                let uu____6356 =
                  let uu____6364 =
                    let uu____6370 =
                      let uu____6371 =
                        let uu____6373 = FStar_Tactics_Types.goal_env g  in
                        let uu____6482 = FStar_Tactics_Types.goal_witness g
                           in
                        tts uu____6373 uu____6482  in
                      FStar_Util.JsonStr uu____6371  in
                    ("witness", uu____6370)  in
                  let uu____6493 =
                    let uu____6501 =
                      let uu____6507 =
                        let uu____6508 =
                          let uu____6510 = FStar_Tactics_Types.goal_env g  in
                          tts uu____6510 g_type1  in
                        FStar_Util.JsonStr uu____6508  in
                      ("type", uu____6507)  in
                    [uu____6501;
                    ("label",
                      (FStar_Util.JsonStr (g.FStar_Tactics_Types.label)))]
                     in
                  uu____6364 :: uu____6493  in
                FStar_Util.JsonAssoc uu____6356  in
              ("goal", uu____6355)  in
            [uu____6349]  in
          ("hyps", j_binders) :: uu____6341  in
        FStar_Util.JsonAssoc uu____6333
  
let (ps_to_json :
  (Prims.string * FStar_Tactics_Types.proofstate) -> FStar_Util.json) =
  fun uu____6739  ->
    match uu____6739 with
    | (msg,ps) ->
        let uu____6950 =
          let uu____6958 =
            let uu____6966 =
              let uu____6974 =
                let uu____6982 =
                  let uu____6988 =
                    let uu____6989 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____6989  in
                  ("goals", uu____6988)  in
                let uu____7053 =
                  let uu____7061 =
                    let uu____7067 =
                      let uu____7068 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____7068  in
                    ("smt-goals", uu____7067)  in
                  [uu____7061]  in
                uu____6982 :: uu____7053  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____6974
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____6966  in
          let uu____7161 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____7177 =
                let uu____7183 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____7183)  in
              [uu____7177]
            else []  in
          FStar_List.append uu____6958 uu____7161  in
        FStar_Util.JsonAssoc uu____6950
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____7357  ->
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
         (let uu____7599 = FStar_Tactics_Types.subst_proof_state subst1 ps
             in
          dump_proofstate uu____7599 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let traise : 'a . Prims.exn -> 'a tac =
  fun e  -> mk_tac (fun ps  -> FStar_Tactics_Result.Failed (e, ps)) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____8220 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____8220
          then dump_proofstate ps (Prims.op_Hat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed
           ((FStar_Tactics_Types.TacticFailure msg), ps))
  
let fail1 : 'Auu____8301 . Prims.string -> Prims.string -> 'Auu____8301 tac =
  fun msg  ->
    fun x  -> let uu____8321 = FStar_Util.format1 msg x  in fail uu____8321
  
let fail2 :
  'Auu____8332 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____8332 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        let uu____8359 = FStar_Util.format2 msg x y  in fail uu____8359
  
let fail3 :
  'Auu____8372 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____8372 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____8406 = FStar_Util.format3 msg x y z  in fail uu____8406
  
let fail4 :
  'Auu____8421 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____8421 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____8462 = FStar_Util.format4 msg x y z w  in
            fail uu____8462
  
let catch : 'a . 'a tac -> (Prims.exn,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____8570 = run t ps  in
         match uu____8570 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___227_9063 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___227_9063.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___227_9063.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___227_9063.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___227_9063.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___227_9063.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___227_9063.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___227_9063.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___227_9063.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___227_9063.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___227_9063.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___227_9063.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (uu___227_9063.FStar_Tactics_Types.local_state)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let recover : 'a . 'a tac -> (Prims.exn,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let uu____9376 = run t ps  in
         match uu____9376 with
         | FStar_Tactics_Result.Success (a,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inr a), q)
         | FStar_Tactics_Result.Failed (m,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inl m), q))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____9832 = catch t  in
    bind uu____9832
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____9865 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try
           (fun uu___253_9970  ->
              match () with
              | () -> let uu____9975 = trytac t  in run uu____9975 ps) ()
         with
         | FStar_Errors.Err (uu____9994,msg) ->
             (log ps
                (fun uu____10000  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____10073,msg,uu____10075) ->
             (log ps
                (fun uu____10080  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____10257 = run t ps  in
           match uu____10257 with
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
  fun p  -> mk_tac (fun uu____11024  -> FStar_Tactics_Result.Success ((), p)) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___288_11313 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___288_11313.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___288_11313.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___288_11313.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___288_11313.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___288_11313.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___288_11313.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___288_11313.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___288_11313.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___288_11313.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___288_11313.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___288_11313.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___288_11313.FStar_Tactics_Types.local_state)
            }))
  
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____11605 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____11605
         then
           let uu____11609 = FStar_Syntax_Print.term_to_string t1  in
           let uu____11611 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____11609
             uu____11611
         else ());
        (try
           (fun uu___296_11625  ->
              match () with
              | () ->
                  let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
                  ((let uu____11640 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____11640
                    then
                      let uu____11644 =
                        FStar_Common.string_of_option
                          (FStar_TypeChecker_Rel.guard_to_string env) res
                         in
                      let uu____11650 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____11652 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.print3
                        "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____11644
                        uu____11650 uu____11652
                    else ());
                   (match res with
                    | FStar_Pervasives_Native.None  -> ret false
                    | FStar_Pervasives_Native.Some g ->
                        let uu____11678 =
                          add_implicits g.FStar_TypeChecker_Env.implicits  in
                        bind uu____11678 (fun uu____11686  -> ret true)))) ()
         with
         | FStar_Errors.Err (uu____11699,msg) ->
             mlog
               (fun uu____11705  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____11708  -> ret false)
         | FStar_Errors.Error (uu____11711,msg,r) ->
             mlog
               (fun uu____11719  ->
                  let uu____11720 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____11720) (fun uu____11724  -> ret false))
  
let (compress_implicits : unit tac) =
  bind get
    (fun ps  ->
       let imps = ps.FStar_Tactics_Types.all_implicits  in
       let g =
         let uu___322_11883 = FStar_TypeChecker_Env.trivial_guard  in
         {
           FStar_TypeChecker_Env.guard_f =
             (uu___322_11883.FStar_TypeChecker_Env.guard_f);
           FStar_TypeChecker_Env.deferred =
             (uu___322_11883.FStar_TypeChecker_Env.deferred);
           FStar_TypeChecker_Env.univ_ineqs =
             (uu___322_11883.FStar_TypeChecker_Env.univ_ineqs);
           FStar_TypeChecker_Env.implicits = imps
         }  in
       let g1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g
          in
       let ps' =
         let uu___326_12036 = ps  in
         {
           FStar_Tactics_Types.main_context =
             (uu___326_12036.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___326_12036.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (g1.FStar_TypeChecker_Env.implicits);
           FStar_Tactics_Types.goals =
             (uu___326_12036.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___326_12036.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___326_12036.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___326_12036.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___326_12036.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___326_12036.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___326_12036.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___326_12036.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___326_12036.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___326_12036.FStar_Tactics_Types.local_state)
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
          (fun uu____12327  ->
             (let uu____12329 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____12329
              then
                (FStar_Options.push ();
                 (let uu____12334 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____12338 = __do_unify env t1 t2  in
              bind uu____12338
                (fun r  ->
                   (let uu____12352 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____12352 then FStar_Options.pop () else ());
                   ret r)))
  
let (remove_solved_goals : unit tac) =
  bind get
    (fun ps  ->
       let ps' =
         let uu___341_12637 = ps  in
         let uu____12772 =
           FStar_List.filter
             (fun g  ->
                let uu____12955 = check_goal_solved g  in
                FStar_Option.isNone uu____12955) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___341_12637.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___341_12637.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___341_12637.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____12772;
           FStar_Tactics_Types.smt_goals =
             (uu___341_12637.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___341_12637.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___341_12637.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___341_12637.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___341_12637.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___341_12637.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___341_12637.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___341_12637.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___341_12637.FStar_Tactics_Types.local_state)
         }  in
       set ps')
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____13113 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____13113 with
      | FStar_Pervasives_Native.Some uu____13125 ->
          let uu____13134 =
            let uu____13136 = goal_to_string_verbose goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____13136  in
          fail uu____13134
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____13293 = FStar_Tactics_Types.goal_env goal  in
      let uu____13402 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____13293 solution uu____13402
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____13554 =
         let uu___354_13689 = p  in
         let uu____13824 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___354_13689.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___354_13689.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___354_13689.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____13824;
           FStar_Tactics_Types.smt_goals =
             (uu___354_13689.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___354_13689.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___354_13689.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___354_13689.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___354_13689.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___354_13689.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___354_13689.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___354_13689.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___354_13689.FStar_Tactics_Types.local_state)
         }  in
       set uu____13554)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      mlog
        (fun uu____14204  ->
           let uu____14205 =
             let uu____14207 = FStar_Tactics_Types.goal_witness goal  in
             FStar_Syntax_Print.term_to_string uu____14207  in
           let uu____14216 = FStar_Syntax_Print.term_to_string solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____14205 uu____14216)
        (fun uu____14221  ->
           let uu____14222 = trysolve goal solution  in
           bind uu____14222
             (fun b  ->
                if b
                then bind __dismiss (fun uu____14240  -> remove_solved_goals)
                else
                  (let uu____14243 =
                     let uu____14245 =
                       let uu____14247 = FStar_Tactics_Types.goal_env goal
                          in
                       tts uu____14247 solution  in
                     let uu____14356 =
                       let uu____14358 = FStar_Tactics_Types.goal_env goal
                          in
                       let uu____14467 =
                         FStar_Tactics_Types.goal_witness goal  in
                       tts uu____14358 uu____14467  in
                     let uu____14476 =
                       let uu____14478 = FStar_Tactics_Types.goal_env goal
                          in
                       let uu____14587 = FStar_Tactics_Types.goal_type goal
                          in
                       tts uu____14478 uu____14587  in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____14245 uu____14356 uu____14476
                      in
                   fail uu____14243)))
  
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____14744 = set_solution goal solution  in
      bind uu____14744
        (fun uu____14751  ->
           bind __dismiss (fun uu____14753  -> remove_solved_goals))
  
let (set_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___370_15030 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___370_15030.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___370_15030.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___370_15030.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals = gs;
              FStar_Tactics_Types.smt_goals =
                (uu___370_15030.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___370_15030.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___370_15030.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___370_15030.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___370_15030.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___370_15030.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___370_15030.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___370_15030.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___370_15030.FStar_Tactics_Types.local_state)
            }))
  
let (set_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___374_15441 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___374_15441.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___374_15441.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___374_15441.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___374_15441.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals = gs;
              FStar_Tactics_Types.depth =
                (uu___374_15441.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___374_15441.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___374_15441.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___374_15441.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___374_15441.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___374_15441.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___374_15441.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___374_15441.FStar_Tactics_Types.local_state)
            }))
  
let (dismiss_all : unit tac) = set_goals [] 
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____15771 = FStar_Options.defensive ()  in
    if uu____15771
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____15889 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____15889)
         in
      let b2 =
        b1 &&
          (let uu____15901 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____15901)
         in
      let rec aux b3 e =
        let uu____16032 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____16032 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____16347 =
        (let uu____16351 = aux b2 env  in Prims.op_Negation uu____16351) &&
          (let uu____16354 = FStar_ST.op_Bang nwarn  in
           uu____16354 < (Prims.parse_int "5"))
         in
      (if uu____16347
       then
         ((let uu____16380 =
             let uu____16381 = FStar_Tactics_Types.goal_type g  in
             uu____16381.FStar_Syntax_Syntax.pos  in
           let uu____16392 =
             let uu____16398 =
               let uu____16400 = goal_to_string_verbose g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____16400
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____16398)  in
           FStar_Errors.log_issue uu____16380 uu____16392);
          (let uu____16404 =
             let uu____16406 = FStar_ST.op_Bang nwarn  in
             uu____16406 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____16404))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___396_16792 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___396_16792.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___396_16792.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___396_16792.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___396_16792.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___396_16792.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___396_16792.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___396_16792.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___396_16792.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___396_16792.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___396_16792.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___396_16792.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___396_16792.FStar_Tactics_Types.local_state)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___401_17323 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___401_17323.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___401_17323.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___401_17323.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___401_17323.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___401_17323.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___401_17323.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___401_17323.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___401_17323.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___401_17323.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___401_17323.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___401_17323.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___401_17323.FStar_Tactics_Types.local_state)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___406_17854 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___406_17854.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___406_17854.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___406_17854.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___406_17854.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___406_17854.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___406_17854.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___406_17854.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___406_17854.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___406_17854.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___406_17854.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___406_17854.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___406_17854.FStar_Tactics_Types.local_state)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___411_18385 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___411_18385.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___411_18385.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___411_18385.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___411_18385.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___411_18385.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___411_18385.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___411_18385.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___411_18385.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___411_18385.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___411_18385.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___411_18385.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___411_18385.FStar_Tactics_Types.local_state)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____18714  -> add_goals [g]) 
let (new_uvar :
  Prims.string ->
    env ->
      FStar_Reflection_Data.typ ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar) tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____19009 =
          FStar_TypeChecker_Env.new_implicit_var_aux reason
            typ.FStar_Syntax_Syntax.pos env typ
            FStar_Syntax_Syntax.Allow_untyped FStar_Pervasives_Native.None
           in
        match uu____19009 with
        | (u,ctx_uvar,g_u) ->
            let uu____19114 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____19114
              (fun uu____19138  ->
                 let uu____19139 =
                   let uu____19156 =
                     let uu____19173 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____19173  in
                   (u, uu____19156)  in
                 ret uu____19139)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____19258 = FStar_Syntax_Util.un_squash t1  in
    match uu____19258 with
    | FStar_Pervasives_Native.Some t' ->
        let t'1 = FStar_Syntax_Util.unascribe t'  in
        let uu____19290 =
          let uu____19291 = FStar_Syntax_Subst.compress t'1  in
          uu____19291.FStar_Syntax_Syntax.n  in
        (match uu____19290 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____19307 -> false)
    | uu____19309 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____19334 = FStar_Syntax_Util.un_squash t  in
    match uu____19334 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____19357 =
          let uu____19358 = FStar_Syntax_Subst.compress t'  in
          uu____19358.FStar_Syntax_Syntax.n  in
        (match uu____19357 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____19374 -> false)
    | uu____19376 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____19455  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____20079 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____20079 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____20223 = goal_to_string_verbose hd1  in
                    let uu____20225 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____20223 uu____20225);
                   ret hd1)))
  
let (tadmit_t : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____20311 =
      bind get
        (fun ps  ->
           let uu____20454 = cur_goal ()  in
           bind uu____20454
             (fun g  ->
                (let uu____20641 =
                   let uu____20642 = FStar_Tactics_Types.goal_type g  in
                   uu____20642.FStar_Syntax_Syntax.pos  in
                 let uu____20653 =
                   let uu____20659 =
                     let uu____20661 =
                       goal_to_string "" FStar_Pervasives_Native.None ps g
                        in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____20661
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____20659)  in
                 FStar_Errors.log_issue uu____20641 uu____20653);
                solve' g t))
       in
    FStar_All.pipe_left (wrap_err "tadmit_t") uu____20311
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____20693  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___456_20975 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___456_20975.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___456_20975.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___456_20975.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___456_20975.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___456_20975.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___456_20975.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___456_20975.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___456_20975.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___456_20975.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___456_20975.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___456_20975.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (uu___456_20975.FStar_Tactics_Types.local_state)
           }  in
         let uu____21111 = set ps1  in
         bind uu____21111
           (fun uu____21119  ->
              let uu____21120 = FStar_BigInt.of_int_fs n1  in ret uu____21120))
  
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
              let uu____21406 = env.FStar_TypeChecker_Env.universe_of env phi
                 in
              FStar_Syntax_Util.mk_squash uu____21406 phi  in
            let uu____21407 = new_uvar reason env typ  in
            bind uu____21407
              (fun uu____21508  ->
                 match uu____21508 with
                 | (uu____21589,ctx_uvar) ->
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
             (fun uu____22141  ->
                let uu____22142 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____22142)
             (fun uu____22147  ->
                let e1 =
                  let uu___474_22257 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___474_22257.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___474_22257.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___474_22257.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___474_22257.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___474_22257.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___474_22257.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___474_22257.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___474_22257.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___474_22257.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___474_22257.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___474_22257.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___474_22257.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___474_22257.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___474_22257.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___474_22257.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___474_22257.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___474_22257.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___474_22257.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___474_22257.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___474_22257.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___474_22257.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___474_22257.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___474_22257.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___474_22257.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___474_22257.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___474_22257.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___474_22257.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___474_22257.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___474_22257.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___474_22257.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___474_22257.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___474_22257.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___474_22257.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___474_22257.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___474_22257.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___474_22257.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___474_22257.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___474_22257.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___474_22257.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___474_22257.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___474_22257.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___474_22257.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___478_22392  ->
                     match () with
                     | () ->
                         let uu____22416 =
                           FStar_TypeChecker_TcTerm.type_of_tot_term e1 t  in
                         ret uu____22416) ()
                with
                | FStar_Errors.Err (uu____22482,msg) ->
                    let uu____22486 = tts e1 t  in
                    let uu____22488 =
                      let uu____22490 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____22490
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____22486 uu____22488 msg
                | FStar_Errors.Error (uu____22512,msg,uu____22514) ->
                    let uu____22517 = tts e1 t  in
                    let uu____22519 =
                      let uu____22521 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____22521
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____22517 uu____22519 msg))
  
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
             (fun uu____22890  ->
                let uu____22891 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc_ghost(%s)\n" uu____22891)
             (fun uu____22896  ->
                let e1 =
                  let uu___495_23006 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___495_23006.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___495_23006.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___495_23006.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___495_23006.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___495_23006.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___495_23006.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___495_23006.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___495_23006.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___495_23006.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___495_23006.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___495_23006.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___495_23006.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___495_23006.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___495_23006.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___495_23006.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___495_23006.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___495_23006.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___495_23006.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___495_23006.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___495_23006.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___495_23006.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___495_23006.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___495_23006.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___495_23006.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___495_23006.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___495_23006.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___495_23006.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___495_23006.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___495_23006.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___495_23006.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___495_23006.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___495_23006.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___495_23006.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___495_23006.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___495_23006.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___495_23006.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___495_23006.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___495_23006.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___495_23006.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___495_23006.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___495_23006.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___495_23006.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___499_23144  ->
                     match () with
                     | () ->
                         let uu____23168 =
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e1 t
                            in
                         (match uu____23168 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____23308,msg) ->
                    let uu____23312 = tts e1 t  in
                    let uu____23314 =
                      let uu____23316 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____23316
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____23312 uu____23314 msg
                | FStar_Errors.Error (uu____23338,msg,uu____23340) ->
                    let uu____23343 = tts e1 t  in
                    let uu____23345 =
                      let uu____23347 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____23347
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____23343 uu____23345 msg))
  
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
             (fun uu____23732  ->
                let uu____23733 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____23733)
             (fun uu____23739  ->
                let e1 =
                  let uu___520_23849 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___520_23849.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___520_23849.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___520_23849.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___520_23849.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___520_23849.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___520_23849.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___520_23849.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___520_23849.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___520_23849.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___520_23849.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___520_23849.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___520_23849.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___520_23849.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___520_23849.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___520_23849.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___520_23849.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___520_23849.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___520_23849.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___520_23849.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___520_23849.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___520_23849.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___520_23849.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___520_23849.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___520_23849.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___520_23849.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___520_23849.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___520_23849.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___520_23849.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___520_23849.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___520_23849.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___520_23849.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___520_23849.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___520_23849.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___520_23849.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___520_23849.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___520_23849.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___520_23849.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___520_23849.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___520_23849.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___520_23849.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___520_23849.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___520_23849.FStar_TypeChecker_Env.nbe)
                  }  in
                let e2 =
                  let uu___523_24068 = e1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___523_24068.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___523_24068.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___523_24068.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___523_24068.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___523_24068.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___523_24068.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___523_24068.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___523_24068.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___523_24068.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___523_24068.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___523_24068.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___523_24068.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___523_24068.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___523_24068.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___523_24068.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___523_24068.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___523_24068.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___523_24068.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___523_24068.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___523_24068.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___523_24068.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___523_24068.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___523_24068.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___523_24068.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___523_24068.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___523_24068.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___523_24068.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___523_24068.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___523_24068.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___523_24068.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___523_24068.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___523_24068.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___523_24068.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___523_24068.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___523_24068.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___523_24068.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___523_24068.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___523_24068.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___523_24068.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___523_24068.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___523_24068.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___523_24068.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___527_24207  ->
                     match () with
                     | () ->
                         let uu____24235 =
                           FStar_TypeChecker_TcTerm.tc_term e2 t  in
                         ret uu____24235) ()
                with
                | FStar_Errors.Err (uu____24313,msg) ->
                    let uu____24317 = tts e2 t  in
                    let uu____24319 =
                      let uu____24321 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____24321
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____24317 uu____24319 msg
                | FStar_Errors.Error (uu____24347,msg,uu____24349) ->
                    let uu____24352 = tts e2 t  in
                    let uu____24354 =
                      let uu____24356 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____24356
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____24352 uu____24354 msg))
  
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
  fun uu____24533  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___548_24829 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___548_24829.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___548_24829.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___548_24829.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___548_24829.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___548_24829.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___548_24829.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___548_24829.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___548_24829.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___548_24829.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___548_24829.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___548_24829.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___548_24829.FStar_Tactics_Types.local_state)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____24994 = get_guard_policy ()  in
      bind uu____24994
        (fun old_pol  ->
           let uu____25003 = set_guard_policy pol  in
           bind uu____25003
             (fun uu____25010  ->
                bind t
                  (fun r  ->
                     let uu____25014 = set_guard_policy old_pol  in
                     bind uu____25014 (fun uu____25021  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____25028 = let uu____25095 = cur_goal ()  in trytac uu____25095  in
  bind uu____25028
    (fun uu___0_25282  ->
       match uu___0_25282 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____25527 = FStar_Options.peek ()  in ret uu____25527)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        mlog
          (fun uu____25674  ->
             let uu____25675 = FStar_TypeChecker_Rel.guard_to_string e g  in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason
               uu____25675)
          (fun uu____25680  ->
             let uu____25681 =
               add_implicits g.FStar_TypeChecker_Env.implicits  in
             bind uu____25681
               (fun uu____25688  ->
                  bind getopts
                    (fun opts  ->
                       let uu____25692 =
                         let uu____25693 =
                           FStar_TypeChecker_Rel.simplify_guard e g  in
                         uu____25693.FStar_TypeChecker_Env.guard_f  in
                       match uu____25692 with
                       | FStar_TypeChecker_Common.Trivial  -> ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____25712 = istrivial e f  in
                           if uu____25712
                           then ret ()
                           else
                             bind get
                               (fun ps  ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop  ->
                                      ((let uu____25865 =
                                          let uu____25871 =
                                            let uu____25873 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g
                                               in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____25873
                                             in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____25871)
                                           in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____25865);
                                       ret ())
                                  | FStar_Tactics_Types.Goal  ->
                                      mlog
                                        (fun uu____25879  ->
                                           let uu____25880 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____25880)
                                        (fun uu____25885  ->
                                           let uu____25886 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____25886
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___577_26192 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___577_26192.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___577_26192.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___577_26192.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___577_26192.FStar_Tactics_Types.label)
                                                  }  in
                                                push_goals [goal1]))
                                  | FStar_Tactics_Types.SMT  ->
                                      mlog
                                        (fun uu____26432  ->
                                           let uu____26433 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____26433)
                                        (fun uu____26438  ->
                                           let uu____26439 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____26439
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___584_26745 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___584_26745.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___584_26745.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___584_26745.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___584_26745.FStar_Tactics_Types.label)
                                                  }  in
                                                push_smt_goals [goal1]))
                                  | FStar_Tactics_Types.Force  ->
                                      mlog
                                        (fun uu____26985  ->
                                           let uu____26986 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____26986)
                                        (fun uu____26990  ->
                                           try
                                             (fun uu___591_26998  ->
                                                match () with
                                                | () ->
                                                    let uu____27004 =
                                                      let uu____27006 =
                                                        let uu____27008 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____27008
                                                         in
                                                      Prims.op_Negation
                                                        uu____27006
                                                       in
                                                    if uu____27004
                                                    then
                                                      mlog
                                                        (fun uu____27030  ->
                                                           let uu____27031 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g
                                                              in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____27031)
                                                        (fun uu____27035  ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else ret ()) ()
                                           with
                                           | uu___590_27040 ->
                                               mlog
                                                 (fun uu____27048  ->
                                                    let uu____27049 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g
                                                       in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____27049)
                                                 (fun uu____27053  ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
  
let (tcc : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp tac) =
  fun t  ->
    let uu____27087 =
      let uu____27097 = cur_goal ()  in
      bind uu____27097
        (fun goal  ->
           let uu____27287 =
             let uu____27315 = FStar_Tactics_Types.goal_env goal  in
             __tc_lax uu____27315 t  in
           bind uu____27287
             (fun uu____27455  ->
                match uu____27455 with
                | (uu____27487,lc,uu____27489) ->
                    let uu____27522 = FStar_Syntax_Syntax.lcomp_comp lc  in
                    ret uu____27522))
       in
    FStar_All.pipe_left (wrap_err "tcc") uu____27087
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____27590 =
      let uu____27602 = tcc t  in
      bind uu____27602 (fun c  -> ret (FStar_Syntax_Util.comp_result c))  in
    FStar_All.pipe_left (wrap_err "tc") uu____27590
  
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
            let uu____27817 = mk_irrelevant_goal reason env phi opts label1
               in
            bind uu____27817 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____28130  ->
    let uu____28136 = cur_goal ()  in
    bind uu____28136
      (fun goal  ->
         let uu____28322 =
           let uu____28324 = FStar_Tactics_Types.goal_env goal  in
           let uu____28433 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____28324 uu____28433  in
         if uu____28322
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____28450 =
              let uu____28452 = FStar_Tactics_Types.goal_env goal  in
              let uu____28561 = FStar_Tactics_Types.goal_type goal  in
              tts uu____28452 uu____28561  in
            fail1 "Not a trivial goal: %s" uu____28450))
  
let divide : 'a 'b . FStar_BigInt.t -> 'a tac -> 'b tac -> ('a * 'b) tac =
  fun n1  ->
    fun l  ->
      fun r  ->
        bind get
          (fun p  ->
             let uu____28763 =
               try
                 (fun uu___649_29028  ->
                    match () with
                    | () ->
                        let uu____29160 =
                          let uu____29287 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____29287
                            p.FStar_Tactics_Types.goals
                           in
                        ret uu____29160) ()
               with | uu___648_29475 -> fail "divide: not enough goals"  in
             bind uu____28763
               (fun uu____29869  ->
                  match uu____29869 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___631_30386 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___631_30386.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___631_30386.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___631_30386.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___631_30386.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___631_30386.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___631_30386.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___631_30386.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___631_30386.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___631_30386.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___631_30386.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___631_30386.FStar_Tactics_Types.local_state)
                        }  in
                      let uu____30580 = set lp  in
                      bind uu____30580
                        (fun uu____30591  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___637_30875 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___637_30875.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___637_30875.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___637_30875.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___637_30875.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___637_30875.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___637_30875.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___637_30875.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___637_30875.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___637_30875.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___637_30875.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___637_30875.FStar_Tactics_Types.local_state)
                                       }  in
                                     let uu____31069 = set rp  in
                                     bind uu____31069
                                       (fun uu____31080  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___643_31364 =
                                                        rp'  in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___643_31364.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___643_31364.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___643_31364.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___643_31364.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___643_31364.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___643_31364.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___643_31364.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___643_31364.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___643_31364.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___643_31364.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___643_31364.FStar_Tactics_Types.local_state)
                                                      }  in
                                                    let uu____31676 = set p'
                                                       in
                                                    bind uu____31676
                                                      (fun uu____31687  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____31693 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____31721 = divide FStar_BigInt.one f idtac  in
    bind uu____31721
      (fun uu____31737  -> match uu____31737 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____31980::uu____31981 ->
             let uu____32161 =
               let uu____32173 = map tau  in
               divide FStar_BigInt.one tau uu____32173  in
             bind uu____32161
               (fun uu____32194  ->
                  match uu____32194 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____32251 =
        bind t1
          (fun uu____32259  ->
             let uu____32260 = map t2  in
             bind uu____32260 (fun uu____32271  -> ret ()))
         in
      focus uu____32251
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____32284  ->
    let uu____32290 =
      let uu____32296 = cur_goal ()  in
      bind uu____32296
        (fun goal  ->
           let uu____32485 =
             let uu____32496 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____32496  in
           match uu____32485 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____32528 =
                 let uu____32530 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____32530  in
               if uu____32528
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____32650 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____32650 [b]  in
                  let typ' = FStar_Syntax_Util.comp_result c  in
                  let uu____32792 = new_uvar "intro" env' typ'  in
                  bind uu____32792
                    (fun uu____32836  ->
                       match uu____32836 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c))
                              in
                           let uu____32924 = set_solution goal sol  in
                           bind uu____32924
                             (fun uu____32933  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                    goal.FStar_Tactics_Types.label
                                   in
                                let uu____33053 =
                                  let uu____33059 = bnorm_goal g  in
                                  replace_cur uu____33059  in
                                bind uu____33053 (fun uu____33179  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____33188 =
                 let uu____33190 = FStar_Tactics_Types.goal_env goal  in
                 let uu____33299 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____33190 uu____33299  in
               fail1 "goal is not an arrow (%s)" uu____33188)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____32290
  
let (intro_rec :
  unit -> (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder) tac) =
  fun uu____33334  ->
    let uu____33344 = cur_goal ()  in
    bind uu____33344
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____33543 =
            let uu____33554 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____33554  in
          match uu____33543 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____33590 =
                let uu____33592 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____33592  in
              if uu____33590
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____33622 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____33622
                    in
                 let bs =
                   let uu____33646 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____33646; b]  in
                 let env' =
                   let uu____33800 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____33800 bs  in
                 let uu____33909 =
                   new_uvar "intro_rec" env'
                     (FStar_Syntax_Util.comp_result c)
                    in
                 bind uu____33909
                   (fun uu____33962  ->
                      match uu____33962 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____34029 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____34040 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____34029
                              FStar_Parser_Const.effect_Tot_lid uu____34040
                              [] FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____34105 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____34105 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____34185 =
                                   let uu____34186 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____34186.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____34185
                                  in
                               let uu____34228 = set_solution goal tm  in
                               bind uu____34228
                                 (fun uu____34240  ->
                                    let uu____34241 =
                                      let uu____34247 =
                                        bnorm_goal
                                          (let uu___714_34368 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___714_34368.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___714_34368.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___714_34368.FStar_Tactics_Types.is_guard);
                                             FStar_Tactics_Types.label =
                                               (uu___714_34368.FStar_Tactics_Types.label)
                                           })
                                         in
                                      replace_cur uu____34247  in
                                    bind uu____34241
                                      (fun uu____34493  ->
                                         let uu____34494 =
                                           let uu____34499 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____34499, b)  in
                                         ret uu____34494)))))
          | FStar_Pervasives_Native.None  ->
              let uu____34512 =
                let uu____34514 = FStar_Tactics_Types.goal_env goal  in
                let uu____34623 = FStar_Tactics_Types.goal_type goal  in
                tts uu____34514 uu____34623  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____34512))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____34657 = cur_goal ()  in
    bind uu____34657
      (fun goal  ->
         mlog
           (fun uu____34844  ->
              let uu____34845 =
                let uu____34847 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____34847  in
              FStar_Util.print1 "norm: witness = %s\n" uu____34845)
           (fun uu____34861  ->
              let steps =
                let uu____34865 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____34865
                 in
              let t =
                let uu____34877 = FStar_Tactics_Types.goal_env goal  in
                let uu____34986 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____34877 uu____34986  in
              let uu____34995 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____34995))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____35268 =
          bind get
            (fun ps  ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
                 | g::uu____35421 -> g.FStar_Tactics_Types.opts
                 | uu____35601 -> FStar_Options.peek ()  in
               mlog
                 (fun uu____35669  ->
                    let uu____35670 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____35670)
                 (fun uu____35675  ->
                    let uu____35676 = __tc_lax e t  in
                    bind uu____35676
                      (fun uu____35736  ->
                         match uu____35736 with
                         | (t1,uu____35769,uu____35770) ->
                             let steps =
                               let uu____35806 =
                                 FStar_TypeChecker_Normalize.tr_norm_steps s
                                  in
                               FStar_List.append
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu____35806
                                in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1
                                in
                             mlog
                               (fun uu____35824  ->
                                  let uu____35825 =
                                    FStar_Syntax_Print.term_to_string t2  in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____35825)
                               (fun uu____35829  -> ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____35268
  
let (refine_intro : unit -> unit tac) =
  fun uu____35867  ->
    let uu____35873 =
      let uu____35879 = cur_goal ()  in
      bind uu____35879
        (fun g  ->
           let uu____36066 =
             let uu____36090 = FStar_Tactics_Types.goal_env g  in
             let uu____36199 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____36090
               uu____36199
              in
           match uu____36066 with
           | (uu____36213,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____36427 =
                 let uu____36441 =
                   let uu____36450 =
                     let uu____36451 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____36451]  in
                   FStar_Syntax_Subst.open_term uu____36450 phi  in
                 match uu____36441 with
                 | (bvs,phi1) ->
                     let uu____36508 =
                       let uu____36519 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____36519  in
                     (uu____36508, phi1)
                  in
               (match uu____36427 with
                | (bv1,phi1) ->
                    let uu____36583 =
                      let uu____36648 = FStar_Tactics_Types.goal_env g  in
                      let uu____36757 =
                        let uu____36766 =
                          let uu____36769 =
                            let uu____36770 =
                              let uu____36786 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____36786)  in
                            FStar_Syntax_Syntax.NT uu____36770  in
                          [uu____36769]  in
                        FStar_Syntax_Subst.subst uu____36766 phi1  in
                      mk_irrelevant_goal "refine_intro refinement"
                        uu____36648 uu____36757 g.FStar_Tactics_Types.opts
                        g.FStar_Tactics_Types.label
                       in
                    bind uu____36583
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____36930  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____35873
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____37150 = cur_goal ()  in
      bind uu____37150
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____37501 = FStar_Tactics_Types.goal_env goal  in
               let uu____37610 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____37501 uu____37610
             else FStar_Tactics_Types.goal_env goal  in
           let uu____37621 = __tc env t  in
           bind uu____37621
             (fun uu____37667  ->
                match uu____37667 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____37721  ->
                         let uu____37722 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____37724 =
                           let uu____37726 =
                             FStar_Tactics_Types.goal_env goal  in
                           FStar_TypeChecker_Rel.guard_to_string uu____37726
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____37722 uu____37724)
                      (fun uu____37838  ->
                         let uu____37839 =
                           let uu____37845 =
                             FStar_Tactics_Types.goal_env goal  in
                           proc_guard "__exact typing" uu____37845 guard  in
                         bind uu____37839
                           (fun uu____37956  ->
                              mlog
                                (fun uu____37960  ->
                                   let uu____37961 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____37963 =
                                     let uu____37965 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____37965
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____37961 uu____37963)
                                (fun uu____37977  ->
                                   let uu____37978 =
                                     let uu____37985 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____38094 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____37985 typ uu____38094  in
                                   bind uu____37978
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____38115 =
                                             let uu____38117 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____38117 t1  in
                                           let uu____38226 =
                                             let uu____38228 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____38228 typ  in
                                           let uu____38337 =
                                             let uu____38339 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____38448 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____38339 uu____38448  in
                                           let uu____38457 =
                                             let uu____38459 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____38568 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____38459 uu____38568  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____38115 uu____38226
                                             uu____38337 uu____38457)))))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun try_refine  ->
    fun set_expected_typ1  ->
      fun tm  ->
        let uu____38616 =
          mlog
            (fun uu____38624  ->
               let uu____38625 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____38625)
            (fun uu____38630  ->
               let uu____38631 =
                 let uu____38641 = __exact_now set_expected_typ1 tm  in
                 catch uu____38641  in
               bind uu____38631
                 (fun uu___2_38653  ->
                    match uu___2_38653 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        traise e
                    | FStar_Util.Inl e ->
                        mlog
                          (fun uu____38667  ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____38671  ->
                             let uu____38672 =
                               let uu____38682 =
                                 let uu____38688 =
                                   norm [FStar_Syntax_Embeddings.Delta]  in
                                 bind uu____38688
                                   (fun uu____38696  ->
                                      let uu____38697 = refine_intro ()  in
                                      bind uu____38697
                                        (fun uu____38704  ->
                                           __exact_now set_expected_typ1 tm))
                                  in
                               catch uu____38682  in
                             bind uu____38672
                               (fun uu___1_38711  ->
                                  match uu___1_38711 with
                                  | FStar_Util.Inr r ->
                                      mlog
                                        (fun uu____38723  ->
                                           FStar_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu____38726  -> ret ())
                                  | FStar_Util.Inl uu____38727 ->
                                      mlog
                                        (fun uu____38729  ->
                                           FStar_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu____38732  -> traise e)))))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____38616
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____38796 = f x  in
          bind uu____38796
            (fun y  ->
               let uu____38807 = mapM f xs  in
               bind uu____38807 (fun ys  -> ret (y :: ys)))
  
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
          let uu____39060 = do_unify e ty1 ty2  in
          bind uu____39060
            (fun uu___3_39089  ->
               if uu___3_39089
               then ret acc
               else
                 (let uu____39136 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____39136 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____39180 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____39182 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____39180
                        uu____39182
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____39223 =
                        let uu____39225 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____39225  in
                      if uu____39223
                      then fail "Codomain is effectful"
                      else
                        (let uu____39276 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____39276
                           (fun uu____39347  ->
                              match uu____39347 with
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
      let uu____39729 =
        mlog
          (fun uu____39737  ->
             let uu____39738 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_apply: tm = %s\n" uu____39738)
          (fun uu____39743  ->
             let uu____39744 = cur_goal ()  in
             bind uu____39744
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____40040 = __tc e tm  in
                  bind uu____40040
                    (fun uu____40088  ->
                       match uu____40088 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____40148 =
                             let uu____40174 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____40174  in
                           bind uu____40148
                             (fun uvs  ->
                                let fix_qual q =
                                  match q with
                                  | FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Meta uu____40244)
                                      ->
                                      FStar_Pervasives_Native.Some
                                        (FStar_Syntax_Syntax.Implicit false)
                                  | uu____40252 -> q  in
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____40299  ->
                                       fun w  ->
                                         match uu____40299 with
                                         | (uvt,q,uu____40337) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, (fix_qual q))]) uvs tm1
                                   in
                                let uvset =
                                  let uu____40413 =
                                    FStar_Syntax_Free.new_uv_set ()  in
                                  FStar_List.fold_right
                                    (fun uu____40458  ->
                                       fun s  ->
                                         match uu____40458 with
                                         | (uu____40498,uu____40499,uv) ->
                                             let uu____40525 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                in
                                             FStar_Util.set_union s
                                               uu____40525) uvs uu____40413
                                   in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset  in
                                let uu____40575 = solve' goal w  in
                                bind uu____40575
                                  (fun uu____40583  ->
                                     let uu____40584 =
                                       mapM
                                         (fun uu____40616  ->
                                            match uu____40616 with
                                            | (uvt,q,uv) ->
                                                let uu____40667 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                   in
                                                (match uu____40667 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____40679 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____40692 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv)
                                                        in
                                                     if uu____40692
                                                     then ret ()
                                                     else
                                                       (let uu____40702 =
                                                          let uu____40764 =
                                                            bnorm_goal
                                                              (let uu___875_40885
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___875_40885.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___875_40885.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false;
                                                                 FStar_Tactics_Types.label
                                                                   =
                                                                   (uu___875_40885.FStar_Tactics_Types.label)
                                                               })
                                                             in
                                                          [uu____40764]  in
                                                        add_goals uu____40702)))
                                         uvs
                                        in
                                     bind uu____40584
                                       (fun uu____41126  ->
                                          proc_guard "apply guard" e guard))))))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____39729
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____41194 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____41194
    then
      let uu____41211 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____41242 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____41331 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____41211 with
      | (pre,post) ->
          let post1 =
            let uu____41408 =
              let uu____41423 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____41423]  in
            FStar_Syntax_Util.mk_app post uu____41408  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____41482 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____41482
       then
         let uu____41499 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____41499
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
            let uu____41620 = f x e  in
            bind uu____41620 (fun e'  -> fold_left f e' xs1)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____41652 =
      let uu____41658 =
        bind get
          (fun ps  ->
             mlog
               (fun uu____41802  ->
                  let uu____41803 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____41803)
               (fun uu____41809  ->
                  let is_unit_t t =
                    let uu____41825 =
                      let uu____41826 = FStar_Syntax_Subst.compress t  in
                      uu____41826.FStar_Syntax_Syntax.n  in
                    match uu____41825 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____41843 -> false  in
                  let uu____41845 = cur_goal ()  in
                  bind uu____41845
                    (fun goal  ->
                       let uu____42031 =
                         let uu____42055 = FStar_Tactics_Types.goal_env goal
                            in
                         __tc uu____42055 tm  in
                       bind uu____42031
                         (fun uu____42190  ->
                            match uu____42190 with
                            | (tm1,t,guard) ->
                                let uu____42241 =
                                  FStar_Syntax_Util.arrow_formals_comp t  in
                                (match uu____42241 with
                                 | (bs,comp) ->
                                     let uu____42304 = lemma_or_sq comp  in
                                     (match uu____42304 with
                                      | FStar_Pervasives_Native.None  ->
                                          fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre,post) ->
                                          let uu____42367 =
                                            fold_left
                                              (fun uu____42469  ->
                                                 fun uu____42470  ->
                                                   match (uu____42469,
                                                           uu____42470)
                                                   with
                                                   | ((b,aq),(uvs,imps,subst1))
                                                       ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst1
                                                           b.FStar_Syntax_Syntax.sort
                                                          in
                                                       let uu____42753 =
                                                         is_unit_t b_t  in
                                                       if uu____42753
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
                                                         (let uu____42979 =
                                                            let uu____43001 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            new_uvar
                                                              "apply_lemma"
                                                              uu____43001 b_t
                                                             in
                                                          bind uu____42979
                                                            (fun uu____43168 
                                                               ->
                                                               match uu____43168
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
                                          bind uu____42367
                                            (fun uu____43565  ->
                                               match uu____43565 with
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
                                                   let uu____43752 =
                                                     let uu____43759 =
                                                       FStar_Tactics_Types.goal_env
                                                         goal
                                                        in
                                                     let uu____43868 =
                                                       FStar_Syntax_Util.mk_squash
                                                         FStar_Syntax_Syntax.U_zero
                                                         post1
                                                        in
                                                     let uu____43877 =
                                                       FStar_Tactics_Types.goal_type
                                                         goal
                                                        in
                                                     do_unify uu____43759
                                                       uu____43868
                                                       uu____43877
                                                      in
                                                   bind uu____43752
                                                     (fun b  ->
                                                        if
                                                          Prims.op_Negation b
                                                        then
                                                          let uu____43899 =
                                                            let uu____43901 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            tts uu____43901
                                                              tm1
                                                             in
                                                          let uu____44010 =
                                                            let uu____44012 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            let uu____44121 =
                                                              FStar_Syntax_Util.mk_squash
                                                                FStar_Syntax_Syntax.U_zero
                                                                post1
                                                               in
                                                            tts uu____44012
                                                              uu____44121
                                                             in
                                                          let uu____44130 =
                                                            let uu____44132 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            let uu____44241 =
                                                              FStar_Tactics_Types.goal_type
                                                                goal
                                                               in
                                                            tts uu____44132
                                                              uu____44241
                                                             in
                                                          fail3
                                                            "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                            uu____43899
                                                            uu____44010
                                                            uu____44130
                                                        else
                                                          (let uu____44253 =
                                                             solve' goal
                                                               FStar_Syntax_Util.exp_unit
                                                              in
                                                           bind uu____44253
                                                             (fun uu____44264
                                                                 ->
                                                                let is_free_uvar
                                                                  uv t1 =
                                                                  let free_uvars
                                                                    =
                                                                    let uu____44304
                                                                    =
                                                                    let uu____44315
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____44315
                                                                     in
                                                                    FStar_List.map
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____44304
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
                                                                    let uu____44625
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____44625)
                                                                    goals
                                                                   in
                                                                let checkone
                                                                  t1 goals =
                                                                  let uu____44776
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                  match uu____44776
                                                                  with
                                                                  | (hd1,uu____44803)
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____44846)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____44879
                                                                    -> false)
                                                                   in
                                                                let uu____44881
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
                                                                    let uu____45143
                                                                    = imp  in
                                                                    match uu____45143
                                                                    with
                                                                    | 
                                                                    (term,ctx_uvar)
                                                                    ->
                                                                    let uu____45252
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____45252
                                                                    with
                                                                    | 
                                                                    (hd1,uu____45344)
                                                                    ->
                                                                    let uu____45385
                                                                    =
                                                                    let uu____45386
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____45386.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____45385
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____45464)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___985_45618
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___985_45618.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___985_45618.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___985_45618.FStar_Tactics_Types.is_guard);
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___985_45618.FStar_Tactics_Types.label)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____45916
                                                                    ->
                                                                    mlog
                                                                    (fun
                                                                    uu____45981
                                                                     ->
                                                                    let uu____45982
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                                                     in
                                                                    let uu____45984
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____45982
                                                                    uu____45984)
                                                                    (fun
                                                                    uu____45991
                                                                     ->
                                                                    let env =
                                                                    let uu___990_46101
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___990_46101.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___990_46101.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___990_46101.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___990_46101.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___990_46101.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___990_46101.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___990_46101.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___990_46101.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___990_46101.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___990_46101.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___990_46101.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___990_46101.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___990_46101.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___990_46101.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___990_46101.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___990_46101.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___990_46101.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___990_46101.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___990_46101.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___990_46101.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___990_46101.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___990_46101.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___990_46101.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___990_46101.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___990_46101.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___990_46101.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___990_46101.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___990_46101.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___990_46101.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___990_46101.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___990_46101.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___990_46101.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___990_46101.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___990_46101.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___990_46101.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___990_46101.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___990_46101.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___990_46101.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___990_46101.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___990_46101.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___990_46101.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___990_46101.FStar_TypeChecker_Env.nbe)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let uu____46220
                                                                    =
                                                                    let uu____46226
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____46230
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
                                                                    let uu____46232
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____46230
                                                                    uu____46232
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____46238
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    uu____46226
                                                                    uu____46238
                                                                    g_typ  in
                                                                    bind
                                                                    uu____46220
                                                                    (fun
                                                                    uu____46409
                                                                     ->
                                                                    ret []))))))
                                                                   in
                                                                bind
                                                                  uu____44881
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
                                                                    let uu____46827
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____46827
                                                                    then
                                                                    let uu____46832
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____46832
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
                                                                    let uu____47083
                                                                    =
                                                                    let uu____47085
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____47085
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____47083)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____47094
                                                                    =
                                                                    let uu____47100
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____47100
                                                                    guard  in
                                                                    bind
                                                                    uu____47094
                                                                    (fun
                                                                    uu____47212
                                                                     ->
                                                                    let uu____47213
                                                                    =
                                                                    let uu____47219
                                                                    =
                                                                    let uu____47221
                                                                    =
                                                                    let uu____47223
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____47332
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____47223
                                                                    uu____47332
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____47221
                                                                     in
                                                                    if
                                                                    uu____47219
                                                                    then
                                                                    let uu____47347
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____47347
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    goal.FStar_Tactics_Types.label
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____47213
                                                                    (fun
                                                                    uu____47460
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2)))))))))))))
         in
      focus uu____41658  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____41652
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____47514 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____47514 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____47532::(e1,uu____47534)::(e2,uu____47536)::[])) when
        (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) ||
          (FStar_Ident.lid_equals l FStar_Parser_Const.c_eq2_lid)
        -> FStar_Pervasives_Native.Some (e1, e2)
    | uu____47657 ->
        let uu____47660 = FStar_Syntax_Util.unb2t typ  in
        (match uu____47660 with
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some t ->
             ((let uu____47707 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "GG t = %s\n" uu____47707);
              (let uu____47710 = FStar_Syntax_Util.head_and_args t  in
               match uu____47710 with
               | (hd1,args) ->
                   let uu____47791 =
                     let uu____47810 =
                       let uu____47811 = FStar_Syntax_Subst.compress hd1  in
                       uu____47811.FStar_Syntax_Syntax.n  in
                     (uu____47810, args)  in
                   (match uu____47791 with
                    | (FStar_Syntax_Syntax.Tm_fvar
                       fv,(uu____47851,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit uu____47852))::
                       (e1,FStar_Pervasives_Native.None )::(e2,FStar_Pervasives_Native.None
                                                            )::[])
                        when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.op_Eq
                        ->
                        ((let uu____47964 =
                            FStar_Syntax_Print.term_to_string e1  in
                          let uu____47966 =
                            FStar_Syntax_Print.term_to_string e2  in
                          FStar_Util.print2 "wat %s -- %s\n" uu____47964
                            uu____47966);
                         FStar_Pervasives_Native.Some (e1, e2))
                    | uu____47989 -> FStar_Pervasives_Native.None))))
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____48062 = destruct_eq' typ  in
    match uu____48062 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____48140 = FStar_Syntax_Util.un_squash typ  in
        (match uu____48140 with
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
        let uu____48659 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____48659 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', bv', [])
            else
              (let uu____49337 = aux e'  in
               FStar_Util.map_opt uu____49337
                 (fun uu____49560  ->
                    match uu____49560 with
                    | (e'',bv,bvs) -> (e'', bv, (bv' :: bvs))))
         in
      let uu____49911 = aux e  in
      FStar_Util.map_opt uu____49911
        (fun uu____50134  ->
           match uu____50134 with
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
          let uu____51079 =
            let uu____51154 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____51154  in
          FStar_Util.map_opt uu____51079
            (fun uu____51403  ->
               match uu____51403 with
               | (e0,b11,bvs) ->
                   let s1 bv =
                     let uu___1087_51691 = bv  in
                     let uu____51702 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___1087_51691.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___1087_51691.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____51702
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___1091_51862 =
                       g.FStar_Tactics_Types.goal_ctx_uvar  in
                     let uu____51879 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____51893 =
                       let uu____51904 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____51904  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___1091_51862.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____51879;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____51893;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___1091_51862.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___1091_51862.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___1091_51862.FStar_Syntax_Syntax.ctx_uvar_range);
                       FStar_Syntax_Syntax.ctx_uvar_meta =
                         (uu___1091_51862.FStar_Syntax_Syntax.ctx_uvar_meta)
                     }  in
                   let uu___1094_51913 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1094_51913.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___1094_51913.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___1094_51913.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1094_51913.FStar_Tactics_Types.label)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____52048 =
      let uu____52054 = cur_goal ()  in
      bind uu____52054
        (fun goal  ->
           let uu____52242 = h  in
           match uu____52242 with
           | (bv,uu____52249) ->
               mlog
                 (fun uu____52267  ->
                    let uu____52268 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____52270 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____52268
                      uu____52270)
                 (fun uu____52275  ->
                    let uu____52276 =
                      let uu____52351 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____52351  in
                    match uu____52276 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                        let uu____52745 =
                          destruct_eq bv1.FStar_Syntax_Syntax.sort  in
                        (match uu____52745 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____52795 =
                               let uu____52796 =
                                 FStar_Syntax_Subst.compress x  in
                               uu____52796.FStar_Syntax_Syntax.n  in
                             (match uu____52795 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv2 =
                                    let uu___1117_52853 = bv2  in
                                    let uu____52864 =
                                      FStar_Syntax_Subst.subst s
                                        bv2.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1117_52853.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1117_52853.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____52864
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv1 :: bvs1)  in
                                  let new_goal =
                                    let uu___1121_53024 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____53041 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____53055 =
                                      let uu____53066 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____53066
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___1121_53024.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____53041;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____53055;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___1121_53024.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___1121_53024.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___1121_53024.FStar_Syntax_Syntax.ctx_uvar_range);
                                      FStar_Syntax_Syntax.ctx_uvar_meta =
                                        (uu___1121_53024.FStar_Syntax_Syntax.ctx_uvar_meta)
                                    }  in
                                  replace_cur
                                    (let uu___1124_53077 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___1124_53077.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___1124_53077.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___1124_53077.FStar_Tactics_Types.is_guard);
                                       FStar_Tactics_Types.label =
                                         (uu___1124_53077.FStar_Tactics_Types.label)
                                     })
                              | uu____53196 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____53198 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____52048
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____53248 =
        let uu____53254 = cur_goal ()  in
        bind uu____53254
          (fun goal  ->
             let uu____53445 = b  in
             match uu____53445 with
             | (bv,uu____53452) ->
                 let bv' =
                   let uu____53478 =
                     let uu___1135_53489 = bv  in
                     let uu____53500 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____53500;
                       FStar_Syntax_Syntax.index =
                         (uu___1135_53489.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___1135_53489.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____53478  in
                 let s1 =
                   let uu____53509 =
                     let uu____53510 =
                       let uu____53526 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____53526)  in
                     FStar_Syntax_Syntax.NT uu____53510  in
                   [uu____53509]  in
                 let uu____53548 = subst_goal bv bv' s1 goal  in
                 (match uu____53548 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____53248
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____53821 =
      let uu____53827 = cur_goal ()  in
      bind uu____53827
        (fun goal  ->
           let uu____54016 = b  in
           match uu____54016 with
           | (bv,uu____54023) ->
               let uu____54038 =
                 let uu____54113 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____54113  in
               (match uu____54038 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                    let uu____54507 = FStar_Syntax_Util.type_u ()  in
                    (match uu____54507 with
                     | (ty,u) ->
                         let uu____54531 = new_uvar "binder_retype" e0 ty  in
                         bind uu____54531
                           (fun uu____54577  ->
                              match uu____54577 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___1159_54636 = bv1  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1159_54636.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1159_54636.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____54650 =
                                      let uu____54651 =
                                        let uu____54667 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv1, uu____54667)  in
                                      FStar_Syntax_Syntax.NT uu____54651  in
                                    [uu____54650]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___1164_54716 = b1  in
                                         let uu____54727 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___1164_54716.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___1164_54716.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____54727
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____54855  ->
                                       let new_goal =
                                         let uu____54975 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____55094 =
                                           let uu____55103 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____55103
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____54975 uu____55094
                                          in
                                       let uu____55112 = add_goals [new_goal]
                                          in
                                       bind uu____55112
                                         (fun uu____55238  ->
                                            let uu____55239 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv1.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____55239
                                              goal.FStar_Tactics_Types.opts
                                              goal.FStar_Tactics_Types.label))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____53821
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____55285 =
        let uu____55291 = cur_goal ()  in
        bind uu____55291
          (fun goal  ->
             let uu____55480 = b  in
             match uu____55480 with
             | (bv,uu____55487) ->
                 let uu____55502 =
                   let uu____55577 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____55577  in
                 (match uu____55502 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                      let steps =
                        let uu____55974 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____55974
                         in
                      let sort' =
                        normalize steps e0 bv1.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___1185_55997 = bv1  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___1185_55997.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___1185_55997.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____56122 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____56122))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____55285
  
let (revert : unit -> unit tac) =
  fun uu____56262  ->
    let uu____56268 = cur_goal ()  in
    bind uu____56268
      (fun goal  ->
         let uu____56454 =
           let uu____56520 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____56520  in
         match uu____56454 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____56892 =
                 let uu____56903 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____56903  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____56892
                in
             let uu____56941 = new_uvar "revert" env' typ'  in
             bind uu____56941
               (fun uu____56984  ->
                  match uu____56984 with
                  | (r,u_r) ->
                      let uu____57032 =
                        let uu____57038 =
                          let uu____57047 =
                            let uu____57048 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____57048.FStar_Syntax_Syntax.pos  in
                          let uu____57059 =
                            let uu____57064 =
                              let uu____57065 =
                                let uu____57078 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____57078  in
                              [uu____57065]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____57064  in
                          uu____57059 FStar_Pervasives_Native.None
                            uu____57047
                           in
                        set_solution goal uu____57038  in
                      bind uu____57032
                        (fun uu____57113  ->
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
      let uu____57263 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____57263
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____57310 = cur_goal ()  in
    bind uu____57310
      (fun goal  ->
         mlog
           (fun uu____57498  ->
              let uu____57499 = FStar_Syntax_Print.binder_to_string b  in
              let uu____57501 =
                let uu____57503 =
                  let uu____57505 =
                    let uu____57519 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____57519  in
                  FStar_All.pipe_right uu____57505 FStar_List.length  in
                FStar_All.pipe_right uu____57503 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____57499 uu____57501)
           (fun uu____57658  ->
              let uu____57659 =
                let uu____57734 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____57734  in
              match uu____57659 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bv1,bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____58182 =
                          free_in bv1 bv'.FStar_Syntax_Syntax.sort  in
                        if uu____58182
                        then
                          let uu____58190 =
                            let uu____58192 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____58192
                             in
                          fail uu____58190
                        else check1 bvs2
                     in
                  let uu____58197 =
                    let uu____58199 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv1 uu____58199  in
                  if uu____58197
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____58217 = check1 bvs  in
                     bind uu____58217
                       (fun uu____58226  ->
                          let env' = push_bvs e' bvs  in
                          let uu____58336 =
                            let uu____58358 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____58358  in
                          bind uu____58336
                            (fun uu____58388  ->
                               match uu____58388 with
                               | (ut,uvar_ut) ->
                                   let uu____58436 = set_solution goal ut  in
                                   bind uu____58436
                                     (fun uu____58444  ->
                                        let uu____58445 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                            goal.FStar_Tactics_Types.label
                                           in
                                        replace_cur uu____58445))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____58574  ->
    let uu____58580 = cur_goal ()  in
    bind uu____58580
      (fun goal  ->
         let uu____58766 =
           let uu____58832 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____58832  in
         match uu____58766 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____59011) ->
             let uu____59193 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____59193)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____59212 = cur_goal ()  in
    bind uu____59212
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____59618 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____59618  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____59739  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____59876 = cur_goal ()  in
    bind uu____59876
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____60282 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____60282  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____60403  -> add_goals [g']))
  
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
            let uu____60819 = FStar_Syntax_Subst.compress t  in
            uu____60819.FStar_Syntax_Syntax.n  in
          let uu____60830 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___1369_60851 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___1369_60851.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___1369_60851.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____60830
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____60906 =
                   let uu____60907 = FStar_Syntax_Subst.compress t1  in
                   uu____60907.FStar_Syntax_Syntax.n  in
                 match uu____60906 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____60965 = ff hd1  in
                     bind uu____60965
                       (fun hd2  ->
                          let fa uu____61017 =
                            match uu____61017 with
                            | (a,q) ->
                                let uu____61057 = ff a  in
                                bind uu____61057 (fun a1  -> ret (a1, q))
                             in
                          let uu____61103 = mapM fa args  in
                          bind uu____61103
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____61248 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____61248 with
                      | (bs1,t') ->
                          let uu____61272 =
                            let uu____61282 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____61282 t'  in
                          bind uu____61272
                            (fun t''  ->
                               let uu____61402 =
                                 let uu____61403 =
                                   let uu____61438 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____61452 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____61438, uu____61452, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____61403  in
                               ret uu____61402))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____61599 = ff hd1  in
                     bind uu____61599
                       (fun hd2  ->
                          let ffb br =
                            let uu____61632 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____61632 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____61705 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____61705  in
                                let uu____61814 = ff1 e  in
                                bind uu____61814
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____61855 = mapM ffb brs  in
                          bind uu____61855
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____61928;
                          FStar_Syntax_Syntax.lbtyp = uu____61929;
                          FStar_Syntax_Syntax.lbeff = uu____61930;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____61932;
                          FStar_Syntax_Syntax.lbpos = uu____61933;_}::[]),e)
                     ->
                     let lb =
                       let uu____62042 =
                         let uu____62043 = FStar_Syntax_Subst.compress t1  in
                         uu____62043.FStar_Syntax_Syntax.n  in
                       match uu____62042 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____62062) -> lb
                       | uu____62121 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____62162 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____62162
                         (fun def1  ->
                            ret
                              (let uu___1322_62197 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1322_62197.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1322_62197.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1322_62197.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1322_62197.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1322_62197.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1322_62197.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____62212 = fflb lb  in
                     bind uu____62212
                       (fun lb1  ->
                          let uu____62246 =
                            let uu____62255 =
                              let uu____62256 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____62256]  in
                            FStar_Syntax_Subst.open_term uu____62255 e  in
                          match uu____62246 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____62323 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____62323  in
                              let uu____62432 = ff1 e1  in
                              bind uu____62432
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____62587 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____62587
                         (fun def  ->
                            ret
                              (let uu___1340_62622 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1340_62622.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1340_62622.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1340_62622.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1340_62622.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1340_62622.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1340_62622.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____62637 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____62637 with
                      | (lbs1,e1) ->
                          let uu____62688 = mapM fflb lbs1  in
                          bind uu____62688
                            (fun lbs2  ->
                               let uu____62738 = ff e1  in
                               bind uu____62738
                                 (fun e2  ->
                                    let uu____62761 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____62761 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____62926 = ff t2  in
                     bind uu____62926
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____63000 = ff t2  in
                     bind uu____63000
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____63026 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___1364_63045 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___1364_63045.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___1364_63045.FStar_Syntax_Syntax.vars)
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
              let uu____63378 =
                FStar_TypeChecker_TcTerm.tc_term
                  (let uu___1377_63403 = env  in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___1377_63403.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___1377_63403.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___1377_63403.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___1377_63403.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_sig =
                       (uu___1377_63403.FStar_TypeChecker_Env.gamma_sig);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___1377_63403.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___1377_63403.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___1377_63403.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___1377_63403.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.attrtab =
                       (uu___1377_63403.FStar_TypeChecker_Env.attrtab);
                     FStar_TypeChecker_Env.is_pattern =
                       (uu___1377_63403.FStar_TypeChecker_Env.is_pattern);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___1377_63403.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___1377_63403.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___1377_63403.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___1377_63403.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___1377_63403.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___1377_63403.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___1377_63403.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___1377_63403.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___1377_63403.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax = true;
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___1377_63403.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.phase1 =
                       (uu___1377_63403.FStar_TypeChecker_Env.phase1);
                     FStar_TypeChecker_Env.failhard =
                       (uu___1377_63403.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___1377_63403.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.uvar_subtyping =
                       (uu___1377_63403.FStar_TypeChecker_Env.uvar_subtyping);
                     FStar_TypeChecker_Env.tc_term =
                       (uu___1377_63403.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.type_of =
                       (uu___1377_63403.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___1377_63403.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.check_type_of =
                       (uu___1377_63403.FStar_TypeChecker_Env.check_type_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___1377_63403.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (uu___1377_63403.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (uu___1377_63403.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.fv_delta_depths =
                       (uu___1377_63403.FStar_TypeChecker_Env.fv_delta_depths);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___1377_63403.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (uu___1377_63403.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.splice =
                       (uu___1377_63403.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.postprocess =
                       (uu___1377_63403.FStar_TypeChecker_Env.postprocess);
                     FStar_TypeChecker_Env.is_native_tactic =
                       (uu___1377_63403.FStar_TypeChecker_Env.is_native_tactic);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___1377_63403.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (uu___1377_63403.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (uu___1377_63403.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.nbe =
                       (uu___1377_63403.FStar_TypeChecker_Env.nbe)
                   }) t
                 in
              match uu____63378 with
              | (t1,lcomp,g) ->
                  let uu____63557 =
                    (let uu____63561 =
                       FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                     Prims.op_Negation uu____63561) ||
                      (let uu____63564 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____63564)
                     in
                  if uu____63557
                  then ret t1
                  else
                    (let rewrite_eq =
                       let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                       let uu____63601 = new_uvar "pointwise_rec" env typ  in
                       bind uu____63601
                         (fun uu____63649  ->
                            match uu____63649 with
                            | (ut,uvar_ut) ->
                                (log ps
                                   (fun uu____63705  ->
                                      let uu____63706 =
                                        FStar_Syntax_Print.term_to_string t1
                                         in
                                      let uu____63708 =
                                        FStar_Syntax_Print.term_to_string ut
                                         in
                                      FStar_Util.print2
                                        "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                        uu____63706 uu____63708);
                                 (let uu____63711 =
                                    let uu____63717 =
                                      let uu____63726 =
                                        FStar_TypeChecker_TcTerm.universe_of
                                          env typ
                                         in
                                      FStar_Syntax_Util.mk_eq2 uu____63726
                                        typ t1 ut
                                       in
                                    add_irrelevant_goal
                                      "pointwise_rec equation" env
                                      uu____63717 opts label1
                                     in
                                  bind uu____63711
                                    (fun uu____63734  ->
                                       let uu____63735 =
                                         bind tau
                                           (fun uu____63752  ->
                                              let ut1 =
                                                FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                  env ut
                                                 in
                                              log ps
                                                (fun uu____63766  ->
                                                   let uu____63767 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1
                                                      in
                                                   let uu____63769 =
                                                     FStar_Syntax_Print.term_to_string
                                                       ut1
                                                      in
                                                   FStar_Util.print2
                                                     "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                     uu____63767 uu____63769);
                                              ret ut1)
                                          in
                                       focus uu____63735))))
                        in
                     let uu____63780 = catch rewrite_eq  in
                     bind uu____63780
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
          let uu____64481 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____64481
            (fun t1  ->
               let uu____64501 =
                 f env
                   (let uu___1454_64516 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___1454_64516.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___1454_64516.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____64501
                 (fun uu____64548  ->
                    match uu____64548 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____64594 =
                               let uu____64595 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____64595.FStar_Syntax_Syntax.n  in
                             match uu____64594 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____64663 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____64663
                                   (fun uu____64700  ->
                                      match uu____64700 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____64735 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____64735
                                            (fun uu____64766  ->
                                               match uu____64766 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___1434_64811 =
                                                         t3  in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___1434_64811.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___1434_64811.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____64901 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____64901 with
                                  | (bs1,t') ->
                                      let uu____64935 =
                                        let uu____64949 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____64949 ctrl1 t'
                                         in
                                      bind uu____64935
                                        (fun uu____65080  ->
                                           match uu____65080 with
                                           | (t'',ctrl2) ->
                                               let uu____65114 =
                                                 let uu____65125 =
                                                   let uu___1447_65136 = t4
                                                      in
                                                   let uu____65147 =
                                                     let uu____65148 =
                                                       let uu____65183 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____65197 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____65183,
                                                         uu____65197, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____65148
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____65147;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___1447_65136.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___1447_65136.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____65125, ctrl2)  in
                                               ret uu____65114))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____65308 -> ret (t3, ctrl1))))

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
              let uu____65486 = ctrl_tac_fold f env ctrl t  in
              bind uu____65486
                (fun uu____65518  ->
                   match uu____65518 with
                   | (t1,ctrl1) ->
                       let uu____65548 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____65548
                         (fun uu____65575  ->
                            match uu____65575 with
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
                let uu____65950 =
                  let uu____65961 =
                    add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                      opts label1
                     in
                  bind uu____65961
                    (fun uu____65975  ->
                       let uu____65976 = ctrl t1  in
                       bind uu____65976
                         (fun res  ->
                            let uu____66005 = trivial ()  in
                            bind uu____66005 (fun uu____66017  -> ret res)))
                   in
                bind uu____65950
                  (fun uu____66039  ->
                     match uu____66039 with
                     | (should_rewrite,ctrl1) ->
                         if Prims.op_Negation should_rewrite
                         then ret (t1, ctrl1)
                         else
                           (let uu____66090 =
                              FStar_TypeChecker_TcTerm.tc_term
                                (let uu___1484_66115 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___1484_66115.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___1484_66115.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___1484_66115.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___1484_66115.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___1484_66115.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___1484_66115.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___1484_66115.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___1484_66115.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___1484_66115.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___1484_66115.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___1484_66115.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___1484_66115.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___1484_66115.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___1484_66115.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___1484_66115.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___1484_66115.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___1484_66115.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___1484_66115.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___1484_66115.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___1484_66115.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___1484_66115.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___1484_66115.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___1484_66115.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___1484_66115.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___1484_66115.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___1484_66115.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___1484_66115.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___1484_66115.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___1484_66115.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___1484_66115.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___1484_66115.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___1484_66115.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___1484_66115.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___1484_66115.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___1484_66115.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___1484_66115.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___1484_66115.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___1484_66115.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___1484_66115.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___1484_66115.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___1484_66115.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___1484_66115.FStar_TypeChecker_Env.nbe)
                                 }) t1
                               in
                            match uu____66090 with
                            | (t2,lcomp,g) ->
                                let uu____66273 =
                                  (let uu____66277 =
                                     FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                       lcomp
                                      in
                                   Prims.op_Negation uu____66277) ||
                                    (let uu____66280 =
                                       FStar_TypeChecker_Env.is_trivial g  in
                                     Prims.op_Negation uu____66280)
                                   in
                                if uu____66273
                                then ret (t2, globalStop)
                                else
                                  (let typ =
                                     lcomp.FStar_Syntax_Syntax.res_typ  in
                                   let uu____66319 =
                                     new_uvar "pointwise_rec" env typ  in
                                   bind uu____66319
                                     (fun uu____66371  ->
                                        match uu____66371 with
                                        | (ut,uvar_ut) ->
                                            (log ps
                                               (fun uu____66431  ->
                                                  let uu____66432 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t2
                                                     in
                                                  let uu____66434 =
                                                    FStar_Syntax_Print.term_to_string
                                                      ut
                                                     in
                                                  FStar_Util.print2
                                                    "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                    uu____66432 uu____66434);
                                             (let uu____66437 =
                                                let uu____66443 =
                                                  let uu____66452 =
                                                    FStar_TypeChecker_TcTerm.universe_of
                                                      env typ
                                                     in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____66452 typ t2 ut
                                                   in
                                                add_irrelevant_goal
                                                  "rewrite_rec equation" env
                                                  uu____66443 opts label1
                                                 in
                                              bind uu____66437
                                                (fun uu____66464  ->
                                                   let uu____66465 =
                                                     bind rewriter
                                                       (fun uu____66490  ->
                                                          let ut1 =
                                                            FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                              env ut
                                                             in
                                                          log ps
                                                            (fun uu____66504 
                                                               ->
                                                               let uu____66505
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   t2
                                                                  in
                                                               let uu____66507
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   ut1
                                                                  in
                                                               FStar_Util.print2
                                                                 "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                                 uu____66505
                                                                 uu____66507);
                                                          ret (ut1, ctrl1))
                                                      in
                                                   focus uu____66465)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term -> (Prims.bool * FStar_BigInt.t) tac) ->
    unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____66584 =
        bind get
          (fun ps  ->
             let uu____66731 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____66731 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____67724  ->
                       let uu____67725 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____67725);
                  bind dismiss_all
                    (fun uu____67730  ->
                       let uu____67731 =
                         let uu____67745 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____67745
                           keepGoing gt1
                          in
                       bind uu____67731
                         (fun uu____67867  ->
                            match uu____67867 with
                            | (gt',uu____67882) ->
                                (log ps
                                   (fun uu____67894  ->
                                      let uu____67895 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____67895);
                                 (let uu____67898 = push_goals gs  in
                                  bind uu____67898
                                    (fun uu____67906  ->
                                       let uu____67907 =
                                         let uu____67969 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____67969]  in
                                       add_goals uu____67907)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____66584
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____68245 =
        bind get
          (fun ps  ->
             let uu____68392 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____68392 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____69385  ->
                       let uu____69386 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____69386);
                  bind dismiss_all
                    (fun uu____69391  ->
                       let uu____69392 =
                         let uu____69402 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____69402 gt1
                          in
                       bind uu____69392
                         (fun gt'  ->
                            log ps
                              (fun uu____69526  ->
                                 let uu____69527 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____69527);
                            (let uu____69530 = push_goals gs  in
                             bind uu____69530
                               (fun uu____69538  ->
                                  let uu____69539 =
                                    let uu____69601 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____69601]  in
                                  add_goals uu____69539))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____68245
  
let (trefl : unit -> unit tac) =
  fun uu____69859  ->
    let uu____69865 =
      let uu____69871 = cur_goal ()  in
      bind uu____69871
        (fun g  ->
           let uu____70069 =
             let uu____70078 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____70078  in
           match uu____70069 with
           | FStar_Pervasives_Native.Some t ->
               let uu____70105 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____70105 with
                | (hd1,args) ->
                    let uu____70171 =
                      let uu____70188 =
                        let uu____70189 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____70189.FStar_Syntax_Syntax.n  in
                      (uu____70188, args)  in
                    (match uu____70171 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____70218::(l,uu____70220)::(r,uu____70222)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____70312 =
                           let uu____70319 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____70319 l r  in
                         bind uu____70312
                           (fun b  ->
                              if b
                              then solve' g FStar_Syntax_Util.exp_unit
                              else
                                (let l1 =
                                   let uu____70449 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____70449 l
                                    in
                                 let r1 =
                                   let uu____70567 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____70567 r
                                    in
                                 let uu____70676 =
                                   let uu____70683 =
                                     FStar_Tactics_Types.goal_env g  in
                                   do_unify uu____70683 l1 r1  in
                                 bind uu____70676
                                   (fun b1  ->
                                      if b1
                                      then
                                        solve' g FStar_Syntax_Util.exp_unit
                                      else
                                        (let uu____70804 =
                                           let uu____70806 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____70806 l1  in
                                         let uu____70915 =
                                           let uu____70917 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____70917 r1  in
                                         fail2
                                           "not a trivial equality ((%s) vs (%s))"
                                           uu____70804 uu____70915))))
                     | (hd2,uu____71028) ->
                         let uu____71053 =
                           let uu____71055 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____71055 t  in
                         fail1 "trefl: not an equality (%s)" uu____71053))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____69865
  
let (dup : unit -> unit tac) =
  fun uu____71193  ->
    let uu____71199 = cur_goal ()  in
    bind uu____71199
      (fun g  ->
         let uu____71385 =
           let uu____71407 = FStar_Tactics_Types.goal_env g  in
           let uu____71516 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____71407 uu____71516  in
         bind uu____71385
           (fun uu____71546  ->
              match uu____71546 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___1576_71713 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___1576_71713.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___1576_71713.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___1576_71713.FStar_Tactics_Types.is_guard);
                      FStar_Tactics_Types.label =
                        (uu___1576_71713.FStar_Tactics_Types.label)
                    }  in
                  bind __dismiss
                    (fun uu____71834  ->
                       let uu____71835 =
                         let uu____71841 = FStar_Tactics_Types.goal_env g  in
                         let uu____71950 =
                           let uu____71959 =
                             let uu____71960 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____72069 =
                               FStar_Tactics_Types.goal_type g  in
                             FStar_TypeChecker_TcTerm.universe_of uu____71960
                               uu____72069
                              in
                           let uu____72078 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____72087 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____71959 uu____72078 u
                             uu____72087
                            in
                         add_irrelevant_goal "dup equation" uu____71841
                           uu____71950 g.FStar_Tactics_Types.opts
                           g.FStar_Tactics_Types.label
                          in
                       bind uu____71835
                         (fun uu____72099  ->
                            let uu____72100 = add_goals [g']  in
                            bind uu____72100 (fun uu____72225  -> ret ())))))
  
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
              let uu____72351 = f x y  in
              if uu____72351 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____72374 -> (acc, l11, l21)  in
        let uu____72389 = aux [] l1 l2  in
        match uu____72389 with | (pr,t1,t2) -> ((FStar_List.rev pr), t1, t2)
  
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
      let uu____72900 = get_phi g1  in
      match uu____72900 with
      | FStar_Pervasives_Native.None  -> fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____73044 = get_phi g2  in
          (match uu____73044 with
           | FStar_Pervasives_Native.None  -> fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let uu____73194 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2)
                  in
               (match uu____73194 with
                | (gamma,r1,r2) ->
                    let t1 =
                      let uu____73295 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1)
                         in
                      close_forall_no_univs1 uu____73295 phi1  in
                    let t2 =
                      let uu____73318 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2)
                         in
                      close_forall_no_univs1 uu____73318 phi2  in
                    let uu____73332 =
                      set_solution g1 FStar_Syntax_Util.exp_unit  in
                    bind uu____73332
                      (fun uu____73399  ->
                         let uu____73400 =
                           set_solution g2 FStar_Syntax_Util.exp_unit  in
                         bind uu____73400
                           (fun uu____73469  ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2  in
                              let nenv =
                                let uu___1627_73590 =
                                  FStar_Tactics_Types.goal_env g1  in
                                let uu____73699 =
                                  FStar_Util.smap_create
                                    (Prims.parse_int "100")
                                   in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___1627_73590.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___1627_73590.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___1627_73590.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___1627_73590.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____73699;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___1627_73590.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___1627_73590.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___1627_73590.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___1627_73590.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___1627_73590.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___1627_73590.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___1627_73590.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___1627_73590.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___1627_73590.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___1627_73590.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___1627_73590.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___1627_73590.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___1627_73590.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___1627_73590.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___1627_73590.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___1627_73590.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___1627_73590.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___1627_73590.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___1627_73590.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___1627_73590.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___1627_73590.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___1627_73590.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___1627_73590.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___1627_73590.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___1627_73590.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___1627_73590.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___1627_73590.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___1627_73590.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___1627_73590.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___1627_73590.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___1627_73590.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___1627_73590.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___1627_73590.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___1627_73590.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___1627_73590.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___1627_73590.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___1627_73590.FStar_TypeChecker_Env.nbe)
                                }  in
                              let uu____73703 =
                                mk_irrelevant_goal "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                  g1.FStar_Tactics_Types.label
                                 in
                              bind uu____73703
                                (fun goal  ->
                                   mlog
                                     (fun uu____74011  ->
                                        let uu____74012 =
                                          goal_to_string_verbose g1  in
                                        let uu____74014 =
                                          goal_to_string_verbose g2  in
                                        let uu____74016 =
                                          goal_to_string_verbose goal  in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____74012 uu____74014 uu____74016)
                                     (fun uu____74020  -> ret goal))))))
  
let (join : unit -> unit tac) =
  fun uu____74090  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____74541 =
               set
                 (let uu___1642_74549 = ps  in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___1642_74549.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.main_goal =
                      (uu___1642_74549.FStar_Tactics_Types.main_goal);
                    FStar_Tactics_Types.all_implicits =
                      (uu___1642_74549.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___1642_74549.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___1642_74549.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___1642_74549.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___1642_74549.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___1642_74549.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___1642_74549.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___1642_74549.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___1642_74549.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___1642_74549.FStar_Tactics_Types.local_state)
                  })
                in
             bind uu____74541
               (fun uu____74686  ->
                  let uu____74687 = join_goals g1 g2  in
                  bind uu____74687 (fun g12  -> add_goals [g12]))
         | uu____74990 -> fail "join: less than 2 goals")
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____75071 =
      let uu____75077 = cur_goal ()  in
      bind uu____75077
        (fun g  ->
           FStar_Options.push ();
           (let uu____75270 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____75270);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___1653_75398 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1653_75398.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___1653_75398.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___1653_75398.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1653_75398.FStar_Tactics_Types.label)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____75071
  
let (top_env : unit -> env tac) =
  fun uu____75596  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____76024  ->
    let uu____76031 = cur_goal ()  in
    bind uu____76031
      (fun g  ->
         let uu____76218 =
           (FStar_Options.lax ()) ||
             (let uu____76221 = FStar_Tactics_Types.goal_env g  in
              uu____76221.FStar_TypeChecker_Env.lax)
            in
         ret uu____76218)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____76376 =
        mlog
          (fun uu____76392  ->
             let uu____76393 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____76393)
          (fun uu____76398  ->
             let uu____76399 = cur_goal ()  in
             bind uu____76399
               (fun goal  ->
                  let env =
                    let uu____76699 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____76699 ty  in
                  let uu____76808 = __tc_ghost env tm  in
                  bind uu____76808
                    (fun uu____76858  ->
                       match uu____76858 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____76919  ->
                                let uu____76920 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____76920)
                             (fun uu____76924  ->
                                mlog
                                  (fun uu____76931  ->
                                     let uu____76932 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____76932)
                                  (fun uu____76937  ->
                                     let uu____76938 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____76938
                                       (fun uu____76950  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____76376
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____77127 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____77163 =
              let uu____77185 =
                let uu____77194 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____77194
                 in
              new_uvar "uvar_env.2" env uu____77185  in
            bind uu____77163
              (fun uu____77243  ->
                 match uu____77243 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____77127
        (fun typ  ->
           let uu____77314 = new_uvar "uvar_env" env typ  in
           bind uu____77314
             (fun uu____77360  ->
                match uu____77360 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____77440 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____77704 -> g.FStar_Tactics_Types.opts
             | uu____77884 -> FStar_Options.peek ()  in
           let uu____77946 = FStar_Syntax_Util.head_and_args t  in
           match uu____77946 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____77977);
                FStar_Syntax_Syntax.pos = uu____77978;
                FStar_Syntax_Syntax.vars = uu____77979;_},uu____77980)
               ->
               let env1 =
                 let uu___1707_78162 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___1707_78162.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___1707_78162.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___1707_78162.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___1707_78162.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___1707_78162.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___1707_78162.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___1707_78162.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___1707_78162.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___1707_78162.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___1707_78162.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___1707_78162.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___1707_78162.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___1707_78162.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___1707_78162.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___1707_78162.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___1707_78162.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___1707_78162.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___1707_78162.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___1707_78162.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___1707_78162.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___1707_78162.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___1707_78162.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___1707_78162.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___1707_78162.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___1707_78162.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___1707_78162.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___1707_78162.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___1707_78162.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___1707_78162.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___1707_78162.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___1707_78162.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___1707_78162.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___1707_78162.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___1707_78162.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___1707_78162.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___1707_78162.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___1707_78162.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___1707_78162.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___1707_78162.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___1707_78162.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___1707_78162.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___1707_78162.FStar_TypeChecker_Env.nbe)
                 }  in
               let g =
                 FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false ""  in
               let uu____78392 =
                 let uu____78454 = bnorm_goal g  in [uu____78454]  in
               add_goals uu____78392
           | uu____78691 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____77440
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____78782 = if b then t2 else ret false  in
             bind uu____78782 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____78817 = trytac comp  in
      bind uu____78817
        (fun uu___4_78832  ->
           match uu___4_78832 with
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
        let uu____79010 =
          bind get
            (fun ps  ->
               let uu____79155 = __tc e t1  in
               bind uu____79155
                 (fun uu____79203  ->
                    match uu____79203 with
                    | (t11,ty1,g1) ->
                        let uu____79255 = __tc e t2  in
                        bind uu____79255
                          (fun uu____79303  ->
                             match uu____79303 with
                             | (t21,ty2,g2) ->
                                 let uu____79355 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____79355
                                   (fun uu____79365  ->
                                      let uu____79366 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____79366
                                        (fun uu____79377  ->
                                           let uu____79378 =
                                             do_unify e ty1 ty2  in
                                           let uu____79385 =
                                             do_unify e t11 t21  in
                                           tac_and uu____79378 uu____79385)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____79010
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____79448  ->
             let uu____79449 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____79449
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
        (fun uu____79515  ->
           let uu____79516 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____79516)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____79556 =
      mlog
        (fun uu____79564  ->
           let uu____79565 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____79565)
        (fun uu____79570  ->
           let uu____79571 = cur_goal ()  in
           bind uu____79571
             (fun g  ->
                let uu____79757 =
                  let uu____79781 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____79781 ty  in
                bind uu____79757
                  (fun uu____79913  ->
                     match uu____79913 with
                     | (ty1,uu____79938,guard) ->
                         let uu____79964 =
                           let uu____79970 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____79970 guard  in
                         bind uu____79964
                           (fun uu____80082  ->
                              let uu____80083 =
                                let uu____80090 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____80199 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____80090 uu____80199 ty1  in
                              bind uu____80083
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____80219 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____80219
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops]  in
                                      let ng =
                                        let uu____80352 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____80461 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____80352
                                          uu____80461
                                         in
                                      let nty =
                                        let uu____80479 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____80479 ty1  in
                                      let uu____80588 =
                                        let uu____80595 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____80595 ng nty  in
                                      bind uu____80588
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____80715 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____80715
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____79556
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) Prims.list tac)
  =
  fun s_tm  ->
    let uu____80939 =
      let uu____80954 = cur_goal ()  in
      bind uu____80954
        (fun g  ->
           let uu____81149 =
             let uu____81173 = FStar_Tactics_Types.goal_env g  in
             __tc uu____81173 s_tm  in
           bind uu____81149
             (fun uu____81314  ->
                match uu____81314 with
                | (s_tm1,s_ty,guard) ->
                    let uu____81374 =
                      let uu____81380 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____81380 guard  in
                    bind uu____81374
                      (fun uu____81504  ->
                         let uu____81505 =
                           FStar_Syntax_Util.head_and_args' s_ty  in
                         match uu____81505 with
                         | (h,args) ->
                             let uu____81580 =
                               let uu____81593 =
                                 let uu____81594 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____81594.FStar_Syntax_Syntax.n  in
                               match uu____81593 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____81632;
                                      FStar_Syntax_Syntax.vars = uu____81633;_},us)
                                   -> ret (fv, us)
                               | uu____81660 -> fail "type is not an fv"  in
                             bind uu____81580
                               (fun uu____81690  ->
                                  match uu____81690 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____81729 =
                                        let uu____81737 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____81737 t_lid
                                         in
                                      (match uu____81729 with
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
                                                  (fun uu____81963  ->
                                                     let uu____81964 =
                                                       FStar_Syntax_Subst.open_term
                                                         t_ps t_ty
                                                        in
                                                     match uu____81964 with
                                                     | (t_ps1,t_ty1) ->
                                                         let uu____81997 =
                                                           mapM
                                                             (fun c_lid  ->
                                                                let uu____82160
                                                                  =
                                                                  let uu____82168
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                  FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____82168
                                                                    c_lid
                                                                   in
                                                                match uu____82160
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
                                                                    uu____82659
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
                                                                    let uu____82672
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____82672
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____82778
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____82778
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____82913
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs
                                                                     in
                                                                    (match uu____82913
                                                                    with
                                                                    | 
                                                                    (d_ps,bs1)
                                                                    ->
                                                                    let uu____83086
                                                                    =
                                                                    let uu____83088
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp  in
                                                                    Prims.op_Negation
                                                                    uu____83088
                                                                     in
                                                                    failwhen
                                                                    uu____83086
                                                                    "not total?"
                                                                    (fun
                                                                    uu____83169
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
                                                                    uu___5_83192
                                                                    =
                                                                    match uu___5_83192
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____83196)
                                                                    -> true
                                                                    | 
                                                                    uu____83199
                                                                    -> false
                                                                     in
                                                                    let uu____83203
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____83203
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
                                                                    uu____83501
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
                                                                    uu____83590
                                                                     ->
                                                                    match uu____83590
                                                                    with
                                                                    | 
                                                                    ((bv,uu____83619),
                                                                    (t,uu____83621))
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
                                                                    uu____83742
                                                                     ->
                                                                    match uu____83742
                                                                    with
                                                                    | 
                                                                    ((bv,uu____83781),
                                                                    (t,uu____83783))
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
                                                                    uu____83892
                                                                     ->
                                                                    match uu____83892
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
                                                                    let uu____84099
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___1871_84187
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___1871_84187.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1871_84187.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1871_84187.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___1871_84187.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___1871_84187.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1871_84187.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1871_84187.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1871_84187.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1871_84187.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___1871_84187.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___1871_84187.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___1871_84187.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1871_84187.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1871_84187.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1871_84187.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1871_84187.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1871_84187.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1871_84187.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1871_84187.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___1871_84187.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___1871_84187.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1871_84187.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1871_84187.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1871_84187.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1871_84187.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1871_84187.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1871_84187.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1871_84187.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1871_84187.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1871_84187.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1871_84187.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1871_84187.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1871_84187.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1871_84187.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___1871_84187.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1871_84187.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1871_84187.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___1871_84187.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1871_84187.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1871_84187.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1871_84187.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1871_84187.FStar_TypeChecker_Env.nbe)
                                                                    }) s_ty
                                                                    pat  in
                                                                    match uu____84099
                                                                    with
                                                                    | 
                                                                    (uu____84374,uu____84375,uu____84376,pat_t,uu____84378,_guard_pat)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____84537
                                                                    =
                                                                    let uu____84546
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____84546
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____84537
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____84567
                                                                    =
                                                                    let uu____84581
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____84581]
                                                                     in
                                                                    let uu____84615
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____84567
                                                                    uu____84615
                                                                     in
                                                                    let nty =
                                                                    let uu____84637
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____84637
                                                                     in
                                                                    let uu____84648
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____84648
                                                                    (fun
                                                                    uu____84767
                                                                     ->
                                                                    match uu____84767
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
                                                                    let uu____85029
                                                                    =
                                                                    let uu____85044
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____85044]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____85029
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____85107
                                                                    =
                                                                    let uu____85180
                                                                    =
                                                                    let uu____85188
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2)  in
                                                                    (fv1,
                                                                    uu____85188)
                                                                     in
                                                                    (g', br,
                                                                    uu____85180)
                                                                     in
                                                                    ret
                                                                    uu____85107))))))
                                                                    | 
                                                                    uu____85341
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                             c_lids
                                                            in
                                                         bind uu____81997
                                                           (fun goal_brs  ->
                                                              let uu____85580
                                                                =
                                                                FStar_List.unzip3
                                                                  goal_brs
                                                                 in
                                                              match uu____85580
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
                                                                  let uu____85930
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                  bind
                                                                    uu____85930
                                                                    (
                                                                    fun
                                                                    uu____85947
                                                                     ->
                                                                    let uu____85948
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____85948
                                                                    (fun
                                                                    uu____85964
                                                                     ->
                                                                    ret infos))))
                                            | uu____85974 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____80939
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____86041::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____86071 = init xs  in x :: uu____86071
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____86098 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      let t3 = FStar_Syntax_Util.unlazy_emb t2  in
      match t3.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____86137) -> inspect t4
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____86268 = last args  in
          (match uu____86268 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____86317 =
                 let uu____86318 =
                   let uu____86327 =
                     let uu____86336 =
                       let uu____86341 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____86341  in
                     uu____86336 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____86327, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____86318  in
               FStar_All.pipe_left ret uu____86317)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____86367,uu____86368) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
          let uu____86488 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____86488 with
           | (bs1,t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____86571 =
                      let uu____86572 =
                        let uu____86581 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____86581)  in
                      FStar_Reflection_Data.Tv_Abs uu____86572  in
                    FStar_All.pipe_left ret uu____86571))
      | FStar_Syntax_Syntax.Tm_type uu____86599 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____86648 ->
          let uu____86672 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____86672 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____86754 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____86754 with
           | (b',t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____86857 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____86892 =
            let uu____86893 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____86893  in
          FStar_All.pipe_left ret uu____86892
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____86933 =
            let uu____86934 =
              let uu____86939 =
                let uu____86940 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____86940  in
              (uu____86939, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____86934  in
          FStar_All.pipe_left ret uu____86933
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____87047 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____87079 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____87079 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____87182 ->
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
             | FStar_Util.Inr uu____87306 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____87337 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____87337 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____87434 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____87480 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____87578 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____87578
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____87611 =
                  let uu____87621 =
                    FStar_List.map
                      (fun uu____87637  ->
                         match uu____87637 with
                         | (p1,uu____87646) -> inspect_pat p1) ps
                     in
                  (fv, uu____87621)  in
                FStar_Reflection_Data.Pat_Cons uu____87611
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
              (fun uu___6_87840  ->
                 match uu___6_87840 with
                 | (pat,uu____87874,t5) ->
                     let uu____87914 = inspect_pat pat  in (uu____87914, t5))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____87937 ->
          ((let uu____87939 =
              let uu____87945 =
                let uu____87947 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____87949 = FStar_Syntax_Print.term_to_string t3  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____87947 uu____87949
                 in
              (FStar_Errors.Warning_CantInspect, uu____87945)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____87939);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____86098
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____87989 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____87989
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____88021 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____88021
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____88051 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____88051
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____88097 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____88097
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____88165 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____88165
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____88230 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____88230
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____88315 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____88315
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____88342 =
          let uu____88351 =
            let uu____88358 =
              let uu____88359 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____88359  in
            FStar_Syntax_Syntax.mk uu____88358  in
          uu____88351 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____88342
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____88379 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____88379
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____88467 =
          let uu____88476 =
            let uu____88483 =
              let uu____88484 =
                let uu____88509 =
                  let uu____88520 =
                    let uu____88521 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____88521]  in
                  FStar_Syntax_Subst.close uu____88520 t2  in
                ((false, [lb]), uu____88509)  in
              FStar_Syntax_Syntax.Tm_let uu____88484  in
            FStar_Syntax_Syntax.mk uu____88483  in
          uu____88476 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____88467
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____88679 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____88679 with
         | (lbs,body) ->
             let uu____88748 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____88748)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____88840 =
                let uu____88841 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____88841  in
              FStar_All.pipe_left wrap uu____88840
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____88854 =
                let uu____88855 =
                  let uu____88875 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____88896 = pack_pat p1  in
                         (uu____88896, false)) ps
                     in
                  (fv, uu____88875)  in
                FStar_Syntax_Syntax.Pat_cons uu____88855  in
              FStar_All.pipe_left wrap uu____88854
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
            (fun uu___7_89008  ->
               match uu___7_89008 with
               | (pat,t1) ->
                   let uu____89045 = pack_pat pat  in
                   (uu____89045, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____89135 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____89135
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____89225 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____89225
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____89362 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____89362
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____89468 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____89468
  
let (lget :
  FStar_Reflection_Data.typ -> Prims.string -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun k  ->
      let uu____89533 =
        bind get
          (fun ps  ->
             let uu____89684 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____89684 with
             | FStar_Pervasives_Native.None  -> fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
      FStar_All.pipe_left (wrap_err "lget") uu____89533
  
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit tac)
  =
  fun _ty  ->
    fun k  ->
      fun t  ->
        let uu____89789 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___2169_90067 = ps  in
                 let uu____90202 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t
                    in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___2169_90067.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___2169_90067.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___2169_90067.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___2169_90067.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___2169_90067.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___2169_90067.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___2169_90067.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___2169_90067.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___2169_90067.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___2169_90067.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___2169_90067.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___2169_90067.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____90202
                 }  in
               set ps1)
           in
        FStar_All.pipe_left (wrap_err "lset") uu____89789
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal * FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun typ  ->
      let uu____90485 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____90485 with
      | (u,ctx_uvars,g_u) ->
          let uu____90629 = FStar_List.hd ctx_uvars  in
          (match uu____90629 with
           | (ctx_uvar,uu____90722) ->
               let g =
                 let uu____90858 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____90858 false
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
        let uu____91131 = goal_of_goal_ty env typ  in
        match uu____91131 with
        | (g,g_u) ->
            let ps =
              let uu____91537 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "TacVerbose")
                 in
              let uu____91540 = FStar_Util.psmap_empty ()  in
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
                FStar_Tactics_Types.tac_verb_dbg = uu____91537;
                FStar_Tactics_Types.local_state = uu____91540
              }  in
            let uu____91802 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____91802)
  